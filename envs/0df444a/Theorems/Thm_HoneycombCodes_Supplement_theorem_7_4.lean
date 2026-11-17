-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_7_4
-- name    : HoneycombCodes.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:37:57.072216+00:00
-- url     : https://prove2.me/theorems/64a48ac5-01ac-4379-b14a-cea18c8b9cf0
-- title:
--   Theorem 7.4 — frame-profile moving-projection bound $|C|\le(1-s)m/(d_E(\lambda-s)\Delta(A))$
-- statement:
--   Let a finite group $G$ act transitively on a finite set $X$, fix $o\in X$, $H=\mathrm{Stab}_G(o)$, and let $x\mapsto\ell_x$ be an equivariant unit-vector embedding into a unitary $G$-representation $W$ with real coefficients $t(x,y)=\langle\ell_x,\ell_y\rangle$. Let $E$ be an irreducible unitary $H$-representation of dimension $d_E$, $\Omega$ a finite family of pairwise inequivalent irreducible unitary $G$-representations $V_\omega$ of dimensions $D_\omega$ (no multiplicity-one assumption), and fix a finite edge set of isometric intertwiners $C_e:V_\nu\to W\otimes V_\omega$, parallel ones with orthogonal images. Let $h=(F,A,b,\lambda)$ be a frame-profile certificate (Definition 7.3), $m=\dim F$, $q_\omega=\|A_\omega\|_F^2$ and $\Delta(A)=\sum_\omega q_\omega^2/D_\omega$. If $\lambda>\max\{s,0\}$, then every $C\subseteq X$ with $t(x,y)\le s$ for distinct $x,y\in C$ obeys
--
--   $$
--   |C|\le B(h;s)=\frac{(1-s)m}{d_E(\lambda-s)\Delta(A)} .
--   $$
--
--   In particular, arbitrary Littlewood–Richardson multiplicities are compatible with the moving-projection method; the scalar profile theorem (Theorem 3.1) is the rank-one case.
--
--   Differences from the source:
--
--   - encoding: the transfer operators $T_e$ defined by (81) at every point $x$ → $T_e=C_e^*\circ(\ell_o\otimes\cdot)\circ a$, i.e. (81) at $x=o$; reason: by $G$-equivariance (81) at $o$ determines it at every $x$ (p.36)
--   - encoding: $t(x,y)\in\mathbb R$ → the real part of $\langle\ell_x,\ell_y\rangle$ under the hypothesis that its imaginary part vanishes; reason: the same number
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §7.2, Theorem 7.4, eq. (86), p.37 (PDF 39); setting §7.1, p.36 (PDF 38)

import Mathlib
import Definitions.Def_HoneycombCodes_Supplement_FrameCert

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes.Supplement

/-- **Theorem 7.4 (frame-profile moving-projection bound)**, Gay, Granha Jeronimo, Liu, *The
Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.37 (PDF 39).
In the setting of §7.1 — a finite group `G` acting transitively on a finite set `X`, `o ∈ X`,
`H = Stab_G(o)`, a unitary `G`-representation `W` with an equivariant unit-vector embedding
`x ↦ ℓ_x` whose coefficients `t(x, y) = ⟨ℓ_x, ℓ_y⟩` are real, an irreducible unitary
`H`-representation `E`, a finite family `Ω` of pairwise inequivalent irreducible unitary
`G`-representations (no multiplicity-one assumption) and a finite edge set of isometric
intertwiners `C_e : V_ν → W ⊗ V_ω` (parallel ones with orthogonal images) — let
`h = (F, A, b, λ)` be a frame-profile certificate (Definition 7.3). If `λ > max{s, 0}`, then every
`C ⊆ X` with `t(x, y) ≤ s` for distinct `x, y ∈ C` obeys
`|C| ≤ B(h; s) = (1 − s) m/(d_E (λ − s) Δ(A))` (86).

**Formalization Note.** `G` and `X` are finite types with a Mathlib `MulAction`; `H` is
`MulAction.stabilizer G o` with its inclusion. The §7.1 data and Definition 7.3 are
`IsFrameSetup` (with `ℓ_o = ℓ o`) and `IsFrameCertificate`; `m = dim F`, `d_E = dim E`,
`Δ(A) = Σ_ω q_ω²/D_ω` with `q_ω = ‖A_ω‖²_F` in the `M_ω` inner product `tr(a* b)/d_E` (`boundB`).
`t(x, y)` is the real part of `⟪ℓ x, ℓ y⟫`, whose imaginary part vanishes by hypothesis. The
setup's conditions `‖ℓ_o‖ = 1` and `ℓ_o` fixed by `H` follow from the hypotheses on `ℓ`. -/
theorem theorem_7_4
    {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X] [MulAction G X] (o : X)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρW : Representation ℂ G W) (ℓ : X → W)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρE : Representation ℂ (MulAction.stabilizer G o) E)
    {Ω : Type*} [Fintype Ω] (V : Ω → Type*) [∀ ω, NormedAddCommGroup (V ω)]
    [∀ ω, InnerProductSpace ℂ (V ω)] [∀ ω, FiniteDimensional ℂ (V ω)]
    (ρ : ∀ ω, Representation ℂ G (V ω))
    (Edge : Ω → Ω → Type*) [∀ ω ν, Fintype (Edge ω ν)]
    (C : ∀ ω ν, Edge ω ν → (V ν →ₗ[ℂ] W ⊗[ℂ] V ω))
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : ∀ ω, F →ₗ[ℂ] (E →ₗ[ℂ] V ω)) (b : ∀ ω ν, Edge ω ν → ℂ) (lam s : ℝ)
    (htrans : MulAction.IsPretransitive G X)
    (hequiv : ∀ (g : G) (x : X), ℓ (g • x) = ρW g (ℓ x))
    (hnorm : ∀ x : X, ‖ℓ x‖ = 1)
    (hreal : ∀ x y : X, (⟪ℓ x, ℓ y⟫_ℂ).im = 0)
    (hsetup : IsFrameSetup (MulAction.stabilizer G o).subtype ρW (ℓ o) ρE V ρ Edge C)
    (hcert : IsFrameCertificate (MulAction.stabilizer G o).subtype (ℓ o) ρE V ρ Edge C F A b lam)
    (hlam : max s 0 < lam)
    (Cset : Finset X) (hC : ∀ x ∈ Cset, ∀ y ∈ Cset, x ≠ y → (⟪ℓ x, ℓ y⟫_ℂ).re ≤ s) :
    (Cset.card : ℝ) ≤ boundB V F A lam s := by sorry

end HoneycombCodes.Supplement
