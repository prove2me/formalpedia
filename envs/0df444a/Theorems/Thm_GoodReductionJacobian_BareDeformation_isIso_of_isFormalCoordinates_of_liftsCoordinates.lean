-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates
-- name    : GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/34c9c469-270e-5a31-b165-cfe4a7d3e25e
-- title:
--   Strict isomorphism of the formal groups of a bare deformation
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra, let the structure map $B \to B_1$ be surjective with nilpotent kernel ideal, let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ carrying a relative group law $L_1$ (a functorial group structure on the sections of $f_1$ over arbitrary $B_1$-schemes), let $\hat G_1$ be a $2$-dimensional formal group law over $B_1$, and let $\theta_1$ be a system of formal coordinates for $f_1$ of dimension $2$, i.e. a rule assigning to each $B_1$-algebra $B'$ and each pair $s \in (B')^2$ a section of $f_1$ over $\operatorname{Spec} B'$, assumed compatible with $L_1$ and $\hat G_1$ in the sense that it is natural in $B_1$-algebra maps on nilpotent pairs and that, for every ideal $J$ with $J^{n+1} = 0$, it restricts to a bijection from pairs in $J$ onto the $J$-infinitesimal sections carrying the truncated group law of $\hat G_1$ to $L_1$. Let $D$ be a bare deformation of $(f_1, L_1)$ to $B$: a scheme $D.A \to \operatorname{Spec} B$ with a commutative relative group law $D.L$, smooth and proper with connected fibres and admitting a group law, together with a map $g : A_1 \to D.A$ exhibiting $f_1$ as the pullback of $D.f$ along $\operatorname{Spec}(B \to B_1)$ and compatible with the two multiplications. Let $G$ and $G'$ be deformations of $\hat G_1$ over $B$, that is $2$-dimensional formal group laws over $B$ whose coefficientwise image in $B_1$ is $\hat G_1$, and let $\theta, \theta'$ be formal coordinates for $D.f$ of dimension $2$ realising $D.L$ with formal group laws $G.F$ and $G'.F$ respectively, both lifting $\theta_1$ in the sense that for every $B$-algebra $B''$ which is also a $B_1$-algebra in a scalar tower over $B$ and every nilpotent pair $s$ in $B''$, the section $\theta_1(B'', s)$ followed by $g$ equals $\theta(B'', s)$, respectively $\theta'(B'', s)$. Then there is a homomorphism $\varphi : G.F \to G'.F$ of formal group laws such that: $\varphi$ has a two-sided inverse homomorphism $\psi$, with $\psi \circ \varphi$ and $\varphi \circ \psi$ the identity homomorphisms; each component power series of $\varphi$ maps to $X_i$ under the coefficientwise map $B \to B_1$; and for every $B$-algebra $B''$, every ideal $J \subseteq B''$ with $J^{n+1} = \bot$ and every pair $s$ with entries in $J$, one has $\theta(B'', s) = \theta'(B'', (\operatorname{nilEval}_n(\varphi_i)(s))_i)$, where $\operatorname{nilEval}_n$ evaluates the truncation of a power series in degrees $\le n$ in each variable.
--
--   This is the uniqueness half of the statement that a bare deformation determines its formal group law up to strict isomorphism: two systems of formal coordinates on the deformation that both reduce to the fixed coordinates $\theta_1$ downstairs give strictly isomorphic formal groups, the isomorphism being the identity modulo the kernel of $B \to B_1$. It is used in the analysis of regluings and shifts of bare deformations, in [`GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul`](thm.html#GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul) and [`GoodReductionJacobian.BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub`](thm.html#GoodReductionJacobian.BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D : BareDeformation f₁ L₁ B)
    (G G' : MvFormalGroup.Deformation Ĝ₁ B) (θ θ' : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hθ' : D.L.IsFormalCoordinates G'.F θ')
    (hl : D.LiftsCoordinates θ₁ θ) (hl' : D.LiftsCoordinates θ₁ θ') :
    ∃ φ : MvFormalGroup.Hom G.F G'.F,
      (∃ ψ : MvFormalGroup.Hom G'.F G.F, ψ.comp φ = MvFormalGroup.Hom.id G.F ∧ φ.comp ψ = MvFormalGroup.Hom.id G'.F) ∧
      (∀ i : Fin 2, MvPowerSeries.map (algebraMap B B₁) (φ.toPowerSeries i) = MvPowerSeries.X i) ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (φ.toPowerSeries i) s) := by sorry
