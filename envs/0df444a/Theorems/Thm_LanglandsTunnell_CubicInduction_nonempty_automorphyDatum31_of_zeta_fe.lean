-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_nonempty_automorphyDatum31_of_zeta_fe
-- name    : LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/c68f8af6-03c7-559a-a562-01d7f6c4f8ae
-- title:
--   Converse theorem on GL₃/ℚ with finite exceptional set
-- statement:
--   Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ that is trivial on $\mathbb{Q}$, continuous and nontrivial; let $S$ be a finite set of finite places at each of which the local component `psiLoc` $\psi$ $v$ has `addCharLevel` zero; let $a$ attach to each finite place a natural number with $a_v\ge 1$ for $v\in S$; and let $\omega:\mathbb{A}^\times\to\mathbb{C}^\times$ be continuous, unitary and trivial on principal ideles, with local component at each $v\in S$ trivial on the units $u$ satisfying $|u|=1$ and $|u-1|\le\exp(-(2a_v-1))$. Let $W$ be a continuous function on $\mathrm{GL}_3(\mathbb{A})$ with $W(u(x,y,z)g)=\psi(x+y)W(g)$ for the upper unipotent matrix with entries $x,y,z$ in positions $(1,2),(2,3),(1,3)$, with $W(zg)=\omega(z)W(g)$ for central $z$, satisfying for each $v\in S$ the equivariance $W(g\,k)=\omega_v(k_{22})W(g)$ for $k$ in the congruence set of $k\in\mathrm{GL}_3(\mathcal O_v)$ with $|k_{01}|,|k_{20}|\le\exp(-a_v)$ and $|k_{21}|\le\exp(-2a_v)$, and the vanishing of $\int W(g\,u(0,x,0))\,dx$ over $\{|x|\le\exp(1)\}$ against the self-dual local Haar measure. Assume the mirabolic series $\sum_i W(\gamma_i g)$ and $\sum_i \widetilde W(\gamma_i g)$, indexed by the right cosets of the rational upper unipotent subgroup of $\mathrm{GL}_2$ embedded in $\mathrm{GL}_3$, converge absolutely at every $g$, where $\widetilde W(g)=W(w_3\,{}^t g^{-1})$; that the sum for $W$ is continuous and slowly increasing with respect to `gauge3`, and the sum for $\widetilde W$ is continuous; and the two integrability hypotheses that, for $g$ whose components at the places of $S$ lie in the congruence sets and for all $\sigma$ beyond a bound depending on $g$, the functions $x\mapsto \|W(\iota(\mathrm{diag}(x,1))g)\|\,\|x\|^{\sigma-1}$ and $(x,u)\mapsto\|\widetilde W(\iota(\mathrm{diag}(x,1))\,n_{21}(u)\,w'\,{}^tg^{-1})\|\,\|x\|^{\sigma-1}$ are integrable for idelic Haar measure, respectively its product with adelic additive Haar measure. Let $\lambda_1,\lambda_2$ be functions on the finite places such that at every $p\notin S$ the function $W$ is right invariant under the image of the local maximal compact subgroup of $\mathrm{GL}_3(\mathbb{Q}_p)$ and is a Hecke coset eigenfunction with eigenvalue $\lambda_1(p)$ for $\mathrm{diag}(\varpi_p,1,1)$ and $\lambda_2(p)$ for $\mathrm{diag}(\varpi_p,\varpi_p,1)$. Let $D$, $U$, `gen` be the carrier data entering `productionPinsOf`, and let $c\in\mathbb{C}$ be the inverse of the volume of the adelic box. Finally assume that for every $g$ with components at the places of $S$ in the congruence sets and every continuous unitary idele class character $\chi$ unramified at all $v\in S$ there is an entire function $E$, bounded on vertical strips, agreeing with the zeta integral `globalZeta30` $W\,\chi\,s\,g$ for $\mathrm{Re}\,s$ large and with $c\cdot$`globalZetaDual31` $W\,\chi\,(1-s)\,g$ for $\mathrm{Re}\,s$ small. Then the type `AutomorphyDatum31` for the pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` and the data $\psi,S,a,\omega,W,\lambda_1,\lambda_2$ is nonempty: there exists a continuous function on $\mathrm{GL}_3(\mathbb{A})$, left invariant under $\mathrm{GL}_3(\mathbb{Q})$, with central character $\omega$, of moderate growth, congruence-equivariant at the places of $S$ as above, whose $\psi$-Whittaker coefficient relative to those pins equals $W$ at every $g$ with components at $S$ in the congruence sets, whose double integral over the radical of $P_{21}$ vanishes at every $g$ with components at $S$ in the corresponding parabolic congruence sets, and which at each $p\notin S$ is right invariant under the local maximal compact subgroup and a Hecke coset eigenfunction with eigenvalues $\lambda_1(p)$ and $\lambda_2(p)$.
--
--   This is the converse theorem for $\mathrm{GL}_3$ over $\mathbb{Q}$ in the form allowing a finite exceptional set $S$ of ramified places: the functional equations of the twisted zeta integrals of a Whittaker function produce an automorphic form on $\mathrm{GL}_3(\mathbb{A})$ with that Whittaker coefficient and the prescribed Hecke eigenvalues. It is used in the cubic induction step of the Langlands–Tunnell argument, by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_nonempty_automorphyDatum31_of_zeta_fe.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (_hψS : ∀ v ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) (_ha : ∀ v ∈ S, 1 ≤ a v)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : IsAdmissibleTwist ℚ ω)
    (_hωa : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (2 * a v - 1), localChar ω v u = 1)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hWc : Continuous W)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hWω : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g)
    (_hWK : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (localChar ω v) W)
    (_hWl : ∀ v ∈ S, HasVanishingUnipotentIntegralAlong v W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (_hgrowth : IsModerateGrowth3 ℚ fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g))
    (_hcont : Continuous fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g))
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hcont' : Continuous fun g => ∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i * g))
    (_hint : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          ‖W (iotaGL (diagUnitGL2 x) * g)‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1))
          (NumberField.Idele.idelicHaar ℚ))
    (_hint' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
          ‖dualWhittakerFn3 W
              (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g))‖ *
            (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
          ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) W)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) W (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) W (lam2 p))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (c : ℂ) (_hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (_hfe : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ → (∀ v ∈ S, IsUnramifiedCharAt χ v) →
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ σ₁ σ₂ : ℝ,
          (∀ s : ℂ, σ₁ < s.re → E s = globalZeta30 W χ s g) ∧
          (∀ s : ℂ, s.re < σ₂ → E s = c * globalZetaDual31 W χ (1 - s) g)) :
    Nonempty (AutomorphyDatum31 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ S a ω W lam1 lam2) := by sorry
