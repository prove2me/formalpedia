-- Prove2me | Theorems.Thm_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
-- name    : LanglandsTunnell.not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/af9b94af-b2ed-5e18-9a54-a9f1065aca17
-- title:
--   Base change to the `sylowH` fixed field is not Eisenstein
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism $\mathrm{Gal}(L/\mathbb{Q}) \cong \mathrm{GL}_2(\mathbb{Z}/3)$. Write $E_6$ for the subfield of $L$ fixed by `quatH e`, the intersection of `sylowH e` (the subgroup of those $\gamma$ whose matrix $e\,\gamma$ is the reduction of some member of the set `P16`) with the kernel of $\det \circ e$, and $E_3$ for the subfield fixed by `sylowH e`. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$, i.e. a nonzero level ideal together with functions $a, b$ on the finite places. Let $c_6, u_6, d_{1,6}, d_{2,6}$ be reals with $d_{1,6} < d_{2,6}$, let $T_6$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles of $E_6$, and put $D = \bigcup_{x \in T_6} (\cdot * x)$ applied to the centre-cut Siegel set of $E_6$ with parameters $c_6, u_6, d_{1,6}, d_{2,6}$, whose members are the $g$ with integral finite part, with $\mathrm{localHeight} \ge c_6$ and $\mathrm{xWindowSq} \le u_6^2$ at every infinite place, and with archimedean determinant norms in $[d_{1,6}, d_{2,6}]$. Assume given a Hecke eigensystem $\Phi_6$ over $E_6$ such that the formal base change of $\Phi$ from $\mathbb{Q}$ to $E_6$ — the eigensystem of level $\top$ with $a(\mathfrak{P}) = \mathrm{satakePow}\, f\, (a\mathfrak{p})\,(b\mathfrak{p})$ and $b(\mathfrak{P}) = (b\mathfrak{p})^{f}$, $f$ the inertia degree of $\mathfrak{P}$ over $\mathfrak{p}$ — agrees with $\Phi_6$ at all places outside some finite set, such that $\Phi_6$ is arithmetically genuinely cusp realizable for the production pins attached to $D$, to the levels $N \mapsto \mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, to the Hecke generators $\mathrm{heckeGen}$ and to the adelic box (that is, the eigensystem obtained from $\Phi_6$ by rescaling $b$ by $(\mathrm{cNorm}\,v)^{-1}$ admits a smooth cusp realisation at these data which is genuine), and such that $D$ covers $\mathrm{GL}_2$ of the adeles of $E_6$ modulo left translation by global points and right multiplication by central scalars. Then for every pair $\mu_1, \mu_2$ of continuous homomorphisms from the idele units of $E_3$ to $\mathbb{C}^{\times}$ that are trivial on the image of $E_3^{\times}$, the formal base change of $\Phi$ to $E_3$ does not agree, away from a finite set of places, with the Eisenstein eigensystem of level that of the base change and with $a(v) = \mu_1(\pi_v) + \mu_2(\pi_v)$, $b(v) = \mu_1(\pi_v)\mu_2(\pi_v)$, where $\pi_v$ is the uniformizer idele at $v$.
--
--   This is the non-Eisenstein step of the converse argument in the Langlands–Tunnell route: cuspidality of the eigensystem attached to the $\mathrm{GL}_2(\mathbb{F}_3)$-tower over the non-normal cubic subfield $E_3$ is deduced from genuine cuspidal realizability over the sextic field $E_6$, using transitivity of formal base change in the tower $\mathbb{Q} \subset E_3 \subset E_6$ and the fact that base change carries an Eisenstein table to an Eisenstein table. It feeds the existence statement [`LanglandsTunnell.exists_agreesFormalBaseChange_arithGenuineCuspRealizable_sylowH_of_quatH_of_unitary_resolvent`](thm.html#LanglandsTunnell.exists_agreesFormalBaseChange_arithGenuineCuspRealizable_sylowH_of_quatH_of_unitary_resolvent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (c₆ u₆ d₁₆ d₂₆ : ℝ)
    (T₆ : Finset (AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
    (hd₆ : d₁₆ < d₂₆)
    (Φ₆ : AutomorphicForm.HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) ℂ)
    (h₆ : (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      Φ).AgreesAwayFromFinite Φ₆)
    (hΦ₆ : AutomorphicForm.IsArithGenuineCuspRealizable
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (AutomorphicForm.productionPinsOf ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
        (⋃ x ∈ T₆, (· * x) ''
          AutomorphicForm.WindowedSiegel.centreCutSiegelSet
            ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₁₆ d₂₆)
        (fun N =>
          NumberField.AdelicLevel.levelOne
              (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
              ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) N ⊓
            AutomorphicForm.finiteAdelicGL2Subgroup
              ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
        (fun v =>
          NumberField.AdelicLevel.heckeGen
            (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
            ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) v)
        (NumberField.AdelicBox.adelicBox ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))) Φ₆)
    (hcov₆ : AutomorphicForm.SiegelCovering.CoversModCentre
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (⋃ x ∈ T₆, (· * x) ''
        AutomorphicForm.WindowedSiegel.centreCutSiegelSet
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₁₆ d₂₆)) :
    ∀ (μ₁ μ₂ : (AdeleRing (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)))ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) μ₁ → IsIdeleClassChar (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ)
          (eisensteinTableOf ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ).level (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ).level_ne_bot μ₁ μ₂) := by sorry
