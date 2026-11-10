-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_3_1
-- name    : HoneycombCodes.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:15.525255+00:00
-- url     : https://prove2.me/theorems/7d103ca3-fa71-4d04-8efb-87c20a75f574
-- title:
--   Theorem 3.1 — profile-optimized representation-graph bound
-- statement:
--   Let a finite group $G$ act transitively on a finite set $X$, with base point $o$ and stabilizer $H$, and fix the data of §3: a unitary representation $W$ with an equivariant unit-vector map $x\mapsto\ell_x$ whose matrix coefficients $t(x,y)=\langle\ell_x,\ell_y\rangle$ are real, an irreducible unitary $H$-representation $E$ of dimension $d_E$, a finite family $\Omega$ of pairwise inequivalent irreducible unitary $G$-representations $V_\omega$ ($D_\omega=\dim V_\omega$) containing $E$ with multiplicity one, the moving embeddings, intertwiners and contraction scalars $c_{\omega,\omega'}\ge0$ of (15), $p_{\omega,\omega'}=c_{\omega,\omega'}^2$, and the balance identity.
--
--   If a positive profile $w$ satisfies $\lambda_\Omega(w)>\max\{s,0\}$, then every $C\subseteq X$ with $t(x,y)\le s$ for distinct $x,y\in C$ obeys
--
--   $$
--   |C|\le\frac{1-s}{d_E\bigl(\lambda_\Omega(w)-s\bigr)}\,D_{eff}(w), \tag{17}
--   $$
--
--   where $\lambda_\Omega(w)=\min_\nu \sum_\omega p_{\omega,\nu}w_\omega/w_\nu$ and $D_{eff}(w)=(\sum_\omega w_\omega)^2/\sum_\omega w_\omega^2/D_\omega$.
--
--   This abstract finite-group bound is the source of every coding bound in the paper: Theorem 4.8 specializes it to the hyperoctahedral group acting on the Hamming cube.
--
--   **Formalization Note** $t(x,y)$ is the real part of the complex inner product (real by hypothesis). The final sentence of the theorem ("one may take the infimum of the right-hand side over every positive profile") is a remark and adds no clause.
--
--   Differences from the source:
--
--   - encoding: fibers E_x of the homogeneous bundle and ϕ_{ω,x}[g,u] = gϕ_{ω,o}u; C*(ℓ_x ⊗ ϕ_{ω,x}u) = c ϕ_{ω′,x}u (15) → (15) for every g ∈ G and u ∈ E with x = g·o, in the adjoint-free form ⟪C v′, ℓ_{g·o} ⊗ ρ_ω(g)ϕ_ω u⟫ = c ⟪v′, ρ_{ω′}(g)ϕ_{ω′} u⟫ for all v′; reason: the bundle maps are determined by ϕ_{ω,o}, and the inner-product identity for all v′ is equivalent to the adjoint identity
--   - encoding: dim Hom_H(E, Res V_ω) = 1 → a nonzero H-intertwiner E → V_ω exists and every H-intertwiner is a complex multiple of it; reason: the same condition stated without a module structure on the intertwiner space
--   - encoding: the scalars c_{ω,ω′} produced by multiplicity one, with phases chosen so that c ≥ 0 → intertwiners C and scalars c ≥ 0 taken as data, with (15) as a hypothesis; reason: the paper's choice satisfies the hypotheses; the statement holds for every such choice
--   - generalization: retained edges: exactly the pairs with V_{ω′} occurring in W ⊗ V_ω (p_{ω,ω′} = 0 on missing edges) → an arbitrary relation `retained`, with isometric intertwiners and (15) required only on retained pairs and p = 0 off them; reason: the paper's retained set is one such relation, so the Lean statement specializes to the source's
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §3, Theorem 3.1, eq. (17), p.14 (PDF 16); standing data pp.13–14

import Mathlib
import Definitions.Def_HoneycombCodes_IsMPSetup
import Definitions.Def_HoneycombCodes_lamProfile

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes

/-- **Theorem 3.1 (Profile-Optimized Representation-Graph Bound)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §3, p.14 (PDF 16).
In the standing setting of §3 (`IsMPSetup`), if a positive profile `w` satisfies
`λ_Ω(w) > max{s, 0}`, then every `C ⊆ X` with `t(x, y) ≤ s` for distinct `x, y ∈ C` obeys
`|C| ≤ (1 − s)/(d_E(λ_Ω(w) − s)) · D_eff(w)` (17).

**Formalization Note.** `t(x, y)` is the real part of `⟪ℓ_x, ℓ_y⟫` (real by the setup);
`d_E = dim E`, `D_ω = dim V_ω`; `λ_Ω(w)` and `D_eff(w)` are `lamProfile` and `effDim` of (16)
with `p = pcoef retained c`. The final sentence of the theorem ("one may take the infimum …") is a
remark and adds no clause. -/
theorem theorem_3_1
    {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X] [MulAction G X] (o : X)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρW : Representation ℂ G W) (ℓ : X → W)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρE : Representation ℂ (MulAction.stabilizer G o) E)
    {Ω : Type*} [Fintype Ω] (V : Ω → Type*) [∀ ω, NormedAddCommGroup (V ω)]
    [∀ ω, InnerProductSpace ℂ (V ω)] [∀ ω, FiniteDimensional ℂ (V ω)]
    (ρ : ∀ ω, Representation ℂ G (V ω)) (ϕ : ∀ ω, E →ₗ[ℂ] V ω)
    (retained : Ω → Ω → Prop) (C : ∀ ω ω', V ω' →ₗ[ℂ] (W ⊗[ℂ] V ω)) (c : Ω → Ω → ℝ)
    (hsetup : IsMPSetup o ρW ℓ ρE V ρ ϕ retained C c)
    (s : ℝ) (w : Ω → ℝ) (hw : ∀ ω, 0 < w ω)
    (hlam : max s 0 < lamProfile (pcoef retained c) w)
    (Cset : Finset X) (hC : ∀ x ∈ Cset, ∀ y ∈ Cset, x ≠ y → (⟪ℓ x, ℓ y⟫_ℂ).re ≤ s) :
    (Cset.card : ℝ) ≤
      (1 - s) / ((Module.finrank ℂ E : ℝ) * (lamProfile (pcoef retained c) w - s)) *
        effDim (fun ω => (Module.finrank ℂ (V ω) : ℝ)) w := by sorry

end HoneycombCodes
