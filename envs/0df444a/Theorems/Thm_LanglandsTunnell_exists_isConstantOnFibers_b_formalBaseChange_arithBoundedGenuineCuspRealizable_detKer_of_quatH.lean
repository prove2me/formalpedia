-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
-- name    : LanglandsTunnell.exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/21fb7359-eca4-5a1c-8ba1-8b441c8fb0ea
-- title:
--   Cubic descent of the lift-trace seed to the determinant-kernel field
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, together with a group isomorphism $e:\mathrm{Gal}(L/\mathbb{Q})\xrightarrow{\sim}\mathrm{GL}_2(\mathbb{Z}/3)$; write $E_2$ for the fixed field of `detKer e`, the kernel of $\det\circ e$, and $E_6$ for the fixed field of `quatH e` $=$ `sylowH e` $\sqcap$ `detKer e`, where `sylowH e` consists of those $\gamma$ whose matrix $e\gamma$ is the reduction mod $3$ of an element of the explicit set `P16`. Given reals $c_6,u_6,d_{61},d_{62}$ and a finite set $T_6\subset\mathrm{GL}_2(\mathbb{A}_{E_6})$, and likewise $c_2,u_2,d_{21},d_{22}$ and $T_2\subset\mathrm{GL}_2(\mathbb{A}_{E_2})$, let $W_F$ denote the union over $x\in T$ of the right translates by $x$ of the centre-cut Siegel set of $F$ with floor $c$, window $u$ and archimedean determinant window $[d_1,d_2]$, and let the production pins of $F$ be this $W_F$ together with the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, full central subgroup, level subgroups $N\mapsto$ `levelOne` $N\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen` and the additive Haar measure conditioned on `adelicBox`. Assume: a Hecke eigensystem $\Phi_6$ over $E_6$ with values in $\mathbb{Z}[\sqrt{-2}]$ whose $a$- and $b$-rows agree outside a finite set of places with the trace and determinant of the explicit $\mathrm{GL}_2(\mathbb{Z}[\sqrt{-2}])$-lift of $e$ of the Frobenius seed for `quatH e`; that the image of $\Phi_6$ under $\iota:\mathbb{Z}[\sqrt{-2}]\to\mathbb{C}$, $\sqrt{-2}\mapsto\sqrt{2}\,i$, after dividing its $b$-row by `cNorm`, admits a bounded genuine smooth cusp realization at the $E_6$-pins for the standard additive character; $d_{61}<d_{62}$ and that $W_{E_6}$ meets every $\mathrm{GL}_2(E_6)$-orbit modulo the centre; and $0<c_2$, $0<d_{21}<d_{22}$ with $W_{E_2}$ likewise covering modulo the centre. The conclusion is the existence of a complex Hecke eigensystem $\Phi_2$ over $E_2$ such that: $\Phi_2$ (with $b$ renormalised by `cNorm`) is boundedly genuinely cusp-realizable at the $E_2$-pins for the standard additive character; $\Phi_2$ is constant on fibres over $\mathbb{Q}$, i.e. outside a finite set its $a$- and $b$-values agree at any two primes lying over the same rational prime with the same inertia degree; outside a finite set $\Phi_2.b$ equals $\iota$ of the determinant row of the lift-trace seed for `detKer e`; and the formal base change of $\Phi_2$ to $E_6$ — whose rows at $\mathfrak{P}$ are `satakePow` of the inertia degree applied to the data at the prime below, and $b^{f}$ — agrees outside a finite set with $\iota$ of the lift-trace seed for `quatH e`. The $a$-row of $\Phi_2$ itself is not pinned to the seed.
--
--   This is the cyclic cubic descent step of the Langlands–Tunnell argument in the tetrahedral-type situation: automorphic data over the degree-six fixed field $E_6$ matching the lift-trace seed is descended, through the cubic extension $E_6/E_2$, to data over the quadratic resolvent $E_2$, the descent being pinned by constancy on fibres over $\mathbb{Q}$, by the determinant row and by the formal base-change identity. It feeds the construction of the pair of cusp forms attached to the seed used in the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.lean

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (c₆ u₆ d₆₁ d₆₂ : ℝ) (T₆ : Finset (AdelicGL2 (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e))))
    (c₂ u₂ d₂₁ d₂₂ : ℝ) (T₂ : Finset (AdelicGL2 (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e))))
    (Φ₆ : HeckeEigensystem ↥(fixFld (quatH e)) (Zsqrtd (-2)))
    (h₆ : Φ₆.AgreesAwayFromFinite (P2.liftTraceSeed e (quatH e)))
    (hc₆ : IsArithBoundedGenuineCuspRealizableVia ↥(fixFld (quatH e))
      (productionPinsOf ↥(fixFld (quatH e))
        (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂)
        (fun N => levelOne (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (quatH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) v) (adelicBox ↥(fixFld (quatH e))))
      (StandardAddChar.stdAddChar ↥(fixFld (quatH e))) iotaZsqrtdNegTwo Φ₆)
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : CoversModCentre ↥(fixFld (quatH e))
      (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂))
    (hc₂ : 0 < c₂) (hd₂₁ : 0 < d₂₁) (hd₂ : d₂₁ < d₂₂)
    (hcov₂ : CoversModCentre ↥(fixFld (detKer e))
      (⋃ x ∈ T₂, (· * x) '' centreCutSiegelSet ↥(fixFld (detKer e)) c₂ u₂ d₂₁ d₂₂)) :
    ∃ Φ₂ : HeckeEigensystem ↥(fixFld (detKer e)) ℂ,
      IsArithBoundedGenuineCuspRealizable ↥(fixFld (detKer e))
        (productionPinsOf ↥(fixFld (detKer e))
          (⋃ x ∈ T₂, (· * x) '' centreCutSiegelSet ↥(fixFld (detKer e)) c₂ u₂ d₂₁ d₂₂)
          (fun N => levelOne (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e)) N ⊓
            finiteAdelicGL2Subgroup ↥(fixFld (detKer e)))
          (fun v => heckeGen (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e)) v) (adelicBox ↥(fixFld (detKer e))))
        (StandardAddChar.stdAddChar ↥(fixFld (detKer e))) Φ₂ ∧
      Φ₂.IsConstantOnFibers ℚ ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (detKer e)))), ∀ v ∉ S,
        Φ₂.b v = ((P2.liftTraceSeed e (detKer e)).map iotaZsqrtdNegTwo).b v) ∧
      (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) Φ₂).AgreesAwayFromFinite
        ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo) := by sorry
