-- Prove2me | Theorems.Thm_GoodQLTC_theorem_9_1
-- name    : GoodQLTC.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:54:28.207195+00:00
-- url     : https://prove2.me/theorems/cf409555-2b8d-4721-8f9a-496a719c3a43
-- title:
--   Theorem 9.1: systolic distance and cycle expansion
-- statement:
--   There is a constant $M_h=M_h(t,n_t)\ge1$ such that the following holds in the setting of §9 ($t\ge2$, $0<\rho\le1$, $\tau\ge1$, $X$ regular $\lambda$-expanding with $n_t/n_1\le\tau$, $\mathcal F$ an $\mathbb F_{2^s}$-cosheaf with compatible base codes whose dual local families $\{C^{\perp}_{f,i}\}_{i\in I}$ are universally $\rho$-product-expanding), if $\lambda L\le1/2$. For the chain complex $C_p=\bigoplus_{f\in X(p)}\mathcal F(f)^*$, $\partial_p=(\delta^{p-1})^*$:
--   1. for $1\le p<t$, every representative of a nonzero class in $H_p$ has block weight at least $\eta Z_{t-p}/M_h$;
--   2. for $2\le p<t$ and every $x\in C_p$, $|\partial_px|_b\ge\alpha'_p\,\mathrm{dist}_b(x,\ker\partial_p)$, $\alpha'_p=(M_h^2/\alpha_{t-p}+M_h)^{-1}$.
--
--   **Formalization Note** $M_h$ is chosen after $t$ and $n_t$ only.
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - encoding: chains C_p = ⊕ F(f)^*, ∂_p = (δ^{p−1})^* → chains in the dual stalk bases; ∂_p is the transposed matrix of δ^{p−1}; reason: dual bases identify F(f)^* with F^{d(f)} blockwise, preserving block weights
--   - encoding: dist(x, U) = min_{u∈U} |x − u| in an inequality → existence of a nearest u ∈ U satisfying the inequality; reason: the minimum over a finite nonempty set is attained; same instances
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 9.1, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_etaConst
open Matrix

namespace GoodQLTC

universe u

/-- **Theorem 9.1** (systolic distance and cycle expansion), Gay–Jeronimo, arXiv:2609.20780 (held
version), p.27: there is a constant `M_h = M_h(t, n_t) ≥ 1` such that, if `λL ≤ 1/2`, the following
hold. For `1 ≤ p < t`, every representative of a nonzero class in `H_p` has block weight at least
`η Z_{t−p}/M_h`. For `2 ≤ p < t` and every `x ∈ C_p`, `|∂_p x|_b ≥ α'_p dist_b(x, ker ∂_p)`, where
`α'_p := (M_h²/α_{t−p} + M_h)^{−1}`.

**Formalization Note.** Standing assumptions of §9 (p.27): `t ≥ 2`, `0 < ρ ≤ 1`, `τ ≥ 1`, `X` a
regular, `λ`-expanding `t`-dimensional cubical complex with degrees `2 ≤ n_1 ≤ ⋯ ≤ n_t`,
`n_t/n_1 ≤ τ`, `F` a cosheaf over `F = F_{2^s}` with compatible base codes `D` whose dual local
families `{C^⊥_{f,i}}_{i∈I}` are universally `ρ`-product-expanding. `M_h` is chosen after `t` and
`n_t` only, before the complex, the cosheaf, `ρ`, `τ`, `λ`. Chains `C_p = ⨁_{f∈X(p)} F(f)^*` are
written in the dual stalk bases, so `∂_p := (δ^{p−1})^*` is the transposed matrix and blocks are
faces. A representative of a nonzero class is a cycle not in `im ∂_{p+1}`. -/
theorem theorem_9_1 (t : ℕ) (ht : 2 ≤ t) (nt : ℕ) :
    ∃ Mh : ℝ, 1 ≤ Mh ∧
    ∀ (X : Type) [PartialOrder X] [Fintype X] (φ : X → Fin t → Option Bool) (n : Fin t → ℕ),
    n ⟨t - 1, by omega⟩ = nt → (∀ i, 2 ≤ n i) → Monotone n →
    IsCubicalComplex t φ → IsRegular φ n → ∀ lam : ℝ, IsExpanding φ n lam →
    ∀ (F : Type) [Field F] [Fintype F] (s : ℕ), 1 ≤ s → Fintype.card F = 2 ^ s →
    ∀ (Fs : Cosheaf X F) (m : Fin t → Bool → ℕ), (∀ i b, 0 < m i b ∧ m i b < n i) →
    ∀ D : BaseCodeData φ Fs m, IsCompatible D →
    ∀ ρ τ : ℝ, 0 < ρ → ρ ≤ 1 → 1 ≤ τ →
    (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ →
    (∀ (f : X) (I : Finset (Fin t)), I.Nonempty → I ⊆ codir φ f →
      IsUnivProductExpanding.{u} ρ (fun i : I => dualCode (localCode D f i.1))) →
    lam * LConst t ρ τ ≤ 1 / 2 →
    (∀ p : ℕ, 1 ≤ p → p < t → ∀ x : Cochain φ Fs p F,
      (cobdMat φ Fs (p - 1) p)ᵀ.mulVec x = 0 →
      x ∉ LinearMap.range (cobdMat φ Fs p (p + 1))ᵀ.mulVecLin →
      etaConst t ρ τ * (numFaces φ (t - p) : ℝ) / Mh ≤ (blockWeight x : ℝ)) ∧
    (∀ p : ℕ, 2 ≤ p → p < t → ∀ x : Cochain φ Fs p F,
      ∃ y : Cochain φ Fs p F, (cobdMat φ Fs (p - 1) p)ᵀ.mulVec y = 0 ∧
        (Mh ^ 2 / alphaConst n ρ τ (t - p) + Mh)⁻¹ * (blockWeight (x - y) : ℝ) ≤
          (blockWeight ((cobdMat φ Fs (p - 1) p)ᵀ.mulVec x) : ℝ)) := by sorry

end GoodQLTC
