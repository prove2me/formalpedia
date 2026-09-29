-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero
-- name    : LanglandsTunnell.exists_admitsModulus_gaussSumFn_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/f3d8c136-2706-58f7-b511-31e2d36b4a91
-- title:
--   Non-vanishing Gauss-sum twist at some admitted modulus
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers, let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles of $F$, and let $\Psi$ be a Hecke eigensystem for $F$ with complex values (a nonzero level ideal together with families $a_v,b_v$ indexed by the finite places). Consider the carrier pins `productionPinsOf` assembled from: the region $D=\bigcup_{x\in T}\{gx: g\in \text{centreCutSiegelSet}\}$, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean components have local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$; the compact subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\text{archimedean projection})$; the Hecke generators $v\mapsto \text{heckeGen}(v)$; full centre $Z=\top$; Borel structures and adelic Haar measures, the additive measure being conditioned on the adelic box. Let $R$ be a smooth cuspidal realization of $\Psi$ at these pins (a function on adelic $\mathrm{GL}_2$ which is not identically zero, smooth cuspidal automorphic for a central character, invariant under $\mathrm{levelOne}(\Psi.\mathrm{level})\cap\ker$, and a Hecke and central eigenfunction outside a finite exceptional set), and assume `IsBoundedGenuineCuspRealizationAt` for $R$ with the standard additive character: $R$ is continuous, bounded on the Siegel windows, all its Whittaker coefficients at the pins are integrable, and they are summable over $\alpha\in F$ for each $g$. Let $\eta$ be a homomorphism from the idele units of $F$ to $\mathbb{C}^\times$ and $\mathfrak f$ an ideal of $\mathcal O_F$ such that $\eta$ admits $\mathfrak f$ as modulus, i.e. $\eta(u)=1$ whenever $u$ has trivial archimedean component, unit valuation at every finite place $v$, and $v$-valuation of $u_v-1$ at most $\exp(-\mathrm{ord}_v(\mathfrak f))$. Then there is a nonzero ideal $\mathfrak f_0$ of $\mathcal O_F$, also admitted as a modulus by $\eta$, and an element $g$ of adelic $\mathrm{GL}_2$, such that the Gauss-sum combination $\sum_{u}\mathrm{gaussWt}(\eta,\mathfrak f_0,u)\,R(g\cdot\mathrm{gaussTrans}(\mathfrak f_0,u))$ over the index set $\mathrm{GaussIndex}(F,\mathfrak f_0)$ is nonzero at $g$.
--
--   This is the non-vanishing input for the Gauss-sum (Hecke) model of the twist of a cuspidal automorphic form on $\mathrm{GL}_2$ by an idele class character, as used on the Langlands–Tunnell side of the argument; note that the modulus is existentially quantified, so the assertion is weaker than non-vanishing at the given $\mathfrak f$. It feeds the construction of the twisted realization in [`LanglandsTunnell.exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut`](thm.html#LanglandsTunnell.exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut) and the arithmetically bounded genuine twist in [`LanglandsTunnell.exists_isArithBoundedGenuineCuspRealizable_twist_centreCut`](thm.html#LanglandsTunnell.exists_isArithBoundedGenuineCuspRealizable_twist_centreCut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero.lean

import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem LanglandsTunnell.exists_admitsModulus_gaussSumFn_ne_zero
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Ψ)
    (hR : IsBoundedGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) Ψ R)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣₀ : Ideal (𝓞 F), 𝔣₀ ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣₀ ∧
      ∃ g : AdelicGL2 (𝓞 F) F, AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣₀ R.toFun g ≠ 0 := by sorry
