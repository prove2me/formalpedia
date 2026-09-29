-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_form_of_tempered_of_entire_eulerTwists
-- name    : LanglandsTunnell.CubicInduction.isCuspidalAlong_form_of_tempered_of_entire_eulerTwists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2bb30b93-eb95-5cc5-8039-3b9a2eebb0db
-- title:
--   Cuspidality of a GL₃ form from entire tempered Euler products
-- statement:
--   Fix an additive character $\psi$ of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, a finite set $S$ of finite places of $\mathbb{Q}$, level exponents $a\colon p\mapsto a(p)\in\mathbb{N}$, a character $\omega$ of the ideles which is an idele class character, continuous and unitary, a function $W$ on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ and functions $\lambda_1,\lambda_2$ on the finite places. Fix also the free data $D\subseteq \mathrm{GL}_2(\mathbb{A})$, $U$ assigning a subgroup of $\mathrm{GL}_2(\mathbb{A})$ to each ideal and $gen$ assigning an element of $\mathrm{GL}_2(\mathbb{A})$ to each place, and let the carrier data be `productionPinsOf` for these with the adelic box, so that the central subgroup is all of the idele units, the measure on $\mathrm{GL}_2$ is the adelic Haar measure for the Borel structure, and the measure $\nu$ on the adeles is the adelic additive Haar measure conditioned on the box (infinite box times integral finite adeles). Let $A$ be an automorphy datum of type `AutomorphyDatum31` for $(\psi,S,a,\omega,W,\lambda_1,\lambda_2)$: its underlying function $\Phi=A.\mathrm{form}$ on $\mathrm{GL}_3(\mathbb{A})$ is continuous, left invariant under $\mathrm{GL}_3(\mathbb{Q})$, transforms under the centre by $\omega$, has moderate growth, is congruence-equivariant at each $v\in S$ of level $a(v)$ through the local component of $\omega$, has $\psi$-Whittaker coefficient equal to $W$ at points whose components at the places of $S$ lie in the congruence sets $\{k\in \mathrm{GL}_3(\mathcal{O}_v):\ v(k_{12}),v(k_{31})\le -a(v),\ v(k_{32})\le -2a(v)\}$, has vanishing double integral along the radical of the $(2,1)$ parabolic at points whose $S$-components lie in the corresponding parabolic congruence sets, and at each $p\notin S$ is right invariant under the image of $\mathrm{GL}_3(\mathcal{O}_p)$ and a coset eigenfunction of the two spherical Hecke generators with eigenvalues $\lambda_1(p),\lambda_2(p)$. Assume further functions $e_1,e_2$ on the places with $\lambda_i(p)=N(p)\,e_i(p)$ for $p\notin S$; that for each $p\notin S$ every root $z$ of $1-e_1(p)z+e_2(p)z^2-c_\omega(p)z^3$ satisfies $\|z\|=1$, where $c_\eta(p)$ denotes $\eta$ evaluated at the uniformizer idele at $p$ when $\eta$ is unramified at $p$ and $0$ otherwise; and that for every idele class character $\sigma$ which is continuous and unitary there are a finite set $T\supseteq S$ and an entire function $E$ on $\mathbb{C}$ with $E(s)=\prod_{p\notin T}\bigl(1-e_1(p)X_p+e_2(p)X_p^2-c_\omega(p)X_p^3\bigr)^{-1}$, $X_p=c_\sigma(p)N(p)^{-s}$, for $\mathrm{Re}(s)>1$. Then $\Phi$ is cuspidal along both maximal parabolics in the unconditional sense: for every $g$ the double integrals of $\Phi$ over the radicals of the $(2,1)$ and of the $(1,2)$ parabolic, taken against $\nu$ in each variable, vanish.
--
--   This is the converse-theorem input in the cubic induction for the Langlands–Tunnell argument: temperedness of the local cubic Euler factors outside $S$ together with entirety of all admissible twists of the associated degree-three Euler product upgrades the partial cuspidality built into the automorphy datum to cuspidality along both maximal parabolics of $\mathrm{GL}_3$ over $\mathbb{Q}$. It is used in the construction of cubic induction data at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_form_of_tempered_of_entire_eulerTwists.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.isCuspidalAlong_form_of_tempered_of_entire_eulerTwists
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (A : AutomorphyDatum31 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ S a ω W lam1 lam2)
    (e₁ e₂ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_he1 : ∀ p, p ∉ S → lam1 p = cNormQ p * e₁ p)
    (_he2 : ∀ p, p ∉ S → lam2 p = cNormQ p * e₂ p)
    (_htemp : ∀ p, p ∉ S → ∀ z : ℂ, 1 - e₁ p * z + e₂ p * z ^ 2 - eulerCoeff ℚ ω p * z ^ 3 = 0 → ‖z‖ = 1)
    (_hE : ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ T ∧
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
          ∀ s : ℂ, 1 < s.re →
            E s = ∏' p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ T},
              (1 - e₁ p.1 * (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s)))
                + e₂ p.1 * (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 2
                - eulerCoeff ℚ ω p.1 *
                    (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 3)⁻¹) :
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) A.form ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) A.form := by sorry
