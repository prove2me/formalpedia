-- Prove2me | Theorems.Thm_GoodQLTC_lemma_9_2
-- name    : GoodQLTC.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:51:50.71031+00:00
-- url     : https://prove2.me/theorems/f7efd753-b609-487e-af7c-b34b4766810e
-- title:
--   Lemma 9.2: transfer through a chain homotopy
-- statement:
--   Let $(C^\bullet,d_C)$, $(D^\bullet,d_D)$ be cochain complexes of finite-dimensional spaces with fixed block decompositions, $\phi:C^\bullet\to D^\bullet$, $\psi:D^\bullet\to C^\bullet$ cochain maps and $h^j:C^j\to C^{j-1}$ with
--   $$
--   \psi\phi+\mathrm{id}_C=d_Ch+hd_C, \tag{9.1}
--   $$
--   every graded piece of $\phi,\psi,h$ of block operator norm at most $M\ge1$. Fix $j$.
--   1. If every representative of a nonzero class in $H^j(D)$ has block weight at least $d_0$, then every representative of a nonzero class in $H^j(C)$ has block weight at least $d_0/M$.
--   2. If $\alpha>0$ and $|d_Dy|_b\ge\alpha\,\mathrm{dist}_b(y,\ker d_D^j)$ for every $y\in D^j$, then every $x\in C^j$ satisfies $|d_Cx|_b\ge(M^2/\alpha+M)^{-1}\mathrm{dist}_b(x,\ker d_C^j)$.
--
--   Differences from the source:
--   - generalization: cochain complexes, cochain maps, (9.1) and norm bounds in all degrees → only the degrees j−1, j, j+1 (two differentials each, cochain-map identities there, (9.1) in degree j, norm bounds there); reason: every pair of complexes satisfying the hypotheses in all degrees satisfies them in these degrees
--   - generalization: finite-dimensional F-spaces, F = F_{2^s} → finite-dimensional spaces over any field; reason: the statement for F_{2^s} is the special case
--   - encoding: fixed block decompositions → each space is a direct sum of coordinate blocks F^{c(b)}, block weight = number of nonzero blocks; reason: a block decomposition into subspaces is isomorphic to coordinate blocks, preserving block weights
--   - encoding: dist(x, U) = min_{u∈U} |x − u| in an inequality → existence of a nearest u ∈ U satisfying the inequality; reason: the minimum over a finite nonempty set is attained; same instances
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Lemma 9.2, pp.27–28 (PDF pp.30–31)

import Mathlib
import Definitions.Def_GoodQLTC_cobdMat

namespace GoodQLTC

/-- **Lemma 9.2** (transfer through a homotopy), Gay–Jeronimo, arXiv:2609.20780 (held version),
p.27: let `(C^•, d_C)` and `(D^•, d_D)` be cochain complexes of finite-dimensional `F`-spaces with
fixed block decompositions, `ϕ : C^• → D^•` and `ψ : D^• → C^•` cochain maps and `h^j : C^j →
C^{j−1}` maps with `ψϕ + id_C = d_C h + h d_C` (9.1), every graded piece of `ϕ, ψ, h` of block
operator norm at most `M ≥ 1`. Fix `j`. If every representative of a nonzero class in `H^j(D)` has
block weight at least `d_0`, then every representative of a nonzero class in `H^j(C)` has block
weight at least `d_0/M`. If `α > 0` and `|d_D y|_b ≥ α dist_b(y, ker d_D^j)` for every `y ∈ D^j`,
then every `x ∈ C^j` satisfies `|d_C x|_b ≥ (M²/α + M)^{−1} dist_b(x, ker d_C^j)`.

**Formalization Note.** Only the degrees `j − 1, j, j + 1` enter: `C^{j−1}, C^j, C^{j+1}` are
`C₀, C₁, C₂` (and likewise `D₀, D₁, D₂`), each a direct sum of coordinate blocks
`⨁_{b} F^{c(b)}`, with `|x|_b` the number of nonzero blocks. The hypotheses are imposed in these
degrees only (complexes, cochain-map identities, (9.1) in degree `j`, norm bounds), which every
pair of complexes satisfying the lemma's hypotheses in all degrees does. `F` is any field (the
paper's `F = F_{2^s}`). `‖T‖_b ≤ M` is `|Tx|_b ≤ M|x|_b` for all `x`; `dist_b` is attained, so it
is stated as an existence of a nearest cocycle. -/
theorem lemma_9_2 {F : Type} [Field F]
    {B₀ B₁ B₂ A₀ A₁ A₂ : Type} [Fintype B₀] [Fintype B₁] [Fintype B₂]
    [Fintype A₀] [Fintype A₁] [Fintype A₂]
    {c₀ : B₀ → ℕ} {c₁ : B₁ → ℕ} {c₂ : B₂ → ℕ} {e₀ : A₀ → ℕ} {e₁ : A₁ → ℕ} {e₂ : A₂ → ℕ}
    (dC₀ : ((Σ b, Fin (c₀ b)) → F) →ₗ[F] ((Σ b, Fin (c₁ b)) → F))
    (dC₁ : ((Σ b, Fin (c₁ b)) → F) →ₗ[F] ((Σ b, Fin (c₂ b)) → F))
    (dD₀ : ((Σ a, Fin (e₀ a)) → F) →ₗ[F] ((Σ a, Fin (e₁ a)) → F))
    (dD₁ : ((Σ a, Fin (e₁ a)) → F) →ₗ[F] ((Σ a, Fin (e₂ a)) → F))
    (hC : dC₁ ∘ₗ dC₀ = 0) (hD : dD₁ ∘ₗ dD₀ = 0)
    (ϕ₀ : ((Σ b, Fin (c₀ b)) → F) →ₗ[F] ((Σ a, Fin (e₀ a)) → F))
    (ϕ₁ : ((Σ b, Fin (c₁ b)) → F) →ₗ[F] ((Σ a, Fin (e₁ a)) → F))
    (ϕ₂ : ((Σ b, Fin (c₂ b)) → F) →ₗ[F] ((Σ a, Fin (e₂ a)) → F))
    (ψ₀ : ((Σ a, Fin (e₀ a)) → F) →ₗ[F] ((Σ b, Fin (c₀ b)) → F))
    (ψ₁ : ((Σ a, Fin (e₁ a)) → F) →ₗ[F] ((Σ b, Fin (c₁ b)) → F))
    (ψ₂ : ((Σ a, Fin (e₂ a)) → F) →ₗ[F] ((Σ b, Fin (c₂ b)) → F))
    (h₁ : ((Σ b, Fin (c₁ b)) → F) →ₗ[F] ((Σ b, Fin (c₀ b)) → F))
    (h₂ : ((Σ b, Fin (c₂ b)) → F) →ₗ[F] ((Σ b, Fin (c₁ b)) → F))
    (hϕ₀ : dD₀ ∘ₗ ϕ₀ = ϕ₁ ∘ₗ dC₀) (hϕ₁ : dD₁ ∘ₗ ϕ₁ = ϕ₂ ∘ₗ dC₁)
    (hψ₀ : dC₀ ∘ₗ ψ₀ = ψ₁ ∘ₗ dD₀) (hψ₁ : dC₁ ∘ₗ ψ₁ = ψ₂ ∘ₗ dD₁)
    (hhom : ψ₁ ∘ₗ ϕ₁ + LinearMap.id = dC₀ ∘ₗ h₁ + h₂ ∘ₗ dC₁)
    (M : ℝ) (hM : 1 ≤ M)
    (nϕ₀ : ∀ x, (blockWeight (ϕ₀ x) : ℝ) ≤ M * blockWeight x)
    (nϕ₁ : ∀ x, (blockWeight (ϕ₁ x) : ℝ) ≤ M * blockWeight x)
    (nϕ₂ : ∀ x, (blockWeight (ϕ₂ x) : ℝ) ≤ M * blockWeight x)
    (nψ₀ : ∀ y, (blockWeight (ψ₀ y) : ℝ) ≤ M * blockWeight y)
    (nψ₁ : ∀ y, (blockWeight (ψ₁ y) : ℝ) ≤ M * blockWeight y)
    (nψ₂ : ∀ y, (blockWeight (ψ₂ y) : ℝ) ≤ M * blockWeight y)
    (nh₁ : ∀ x, (blockWeight (h₁ x) : ℝ) ≤ M * blockWeight x)
    (nh₂ : ∀ x, (blockWeight (h₂ x) : ℝ) ≤ M * blockWeight x) :
    (∀ d₀ : ℝ, (∀ y, dD₁ y = 0 → y ∉ LinearMap.range dD₀ → d₀ ≤ blockWeight y) →
      ∀ x, dC₁ x = 0 → x ∉ LinearMap.range dC₀ → d₀ / M ≤ blockWeight x) ∧
    (∀ α : ℝ, 0 < α →
      (∀ y, ∃ y', dD₁ y' = 0 ∧ α * (blockWeight (y - y') : ℝ) ≤ blockWeight (dD₁ y)) →
      ∀ x, ∃ x', dC₁ x' = 0 ∧
        (1 / (M ^ 2 / α + M)) * (blockWeight (x - x') : ℝ) ≤ blockWeight (dC₁ x)) := by sorry

end GoodQLTC
