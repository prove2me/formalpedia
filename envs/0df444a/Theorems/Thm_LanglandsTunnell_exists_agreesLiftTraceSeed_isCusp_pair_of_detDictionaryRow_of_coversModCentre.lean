-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre
-- name    : LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d711b43c-97b8-572b-b7ee-cb8d01dcd6e0
-- title:
--   Octahedral Langlands–Tunnell over ℚ at cubic-resolvent grain
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism from $\mathrm{Gal}(L/\mathbb{Q})$ onto $\mathrm{GL}_2(\mathbb{Z}/3)$ satisfying `DetDictionaryRow`: for every prime $\ell \neq 3$ and every prime ideal $Q$ of $\mathcal{O}_L$ with finite residue ring lying over $\ell$ and with trivial inertia subgroup in $\mathrm{Gal}(L/\mathbb{Q})$, the determinant of the matrix $e(\mathrm{Frob}_Q)$ equals $\ell$ in $\mathbb{Z}/3$. Three subgroups of $\mathrm{Gal}(L/\mathbb{Q})$ enter through their fixed fields inside $L$: `detKer e`, the kernel of $\det \circ e$; `sylowH e`, the set of $\gamma$ whose matrix $e(\gamma)$ is the mod-$3$ reduction of some matrix in the explicit list `P16`; and `quatH e`, their intersection. For each of the three fields $F$ among these fixed fields one is given reals $c,u,d_1,d_2$ with $d_1 < d_2$, $0 < c$, $0 < d_1$, and a finite set $T$ of elements of $\mathrm{GL}_2$ over the adeles of $F$, such that the union of the right translates by $x \in T$ of the centre-cut Siegel set of $F$ with parameters $c,u,d_1,d_2$ (finite part in the integral subgroup, local height at least $c$, squared window coordinate at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place) covers $\mathrm{GL}_2$ of the adeles of $F$ modulo left multiplication by $\mathrm{GL}_2(F)$ and right multiplication by adelic central scalars. The conclusion asserts the existence of a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with values in $\mathbb{Z}[\sqrt{-2}]$ (a level ideal, nonzero, together with eigenvalue functions $a$ and $b$ on the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$) with two properties. First, the formal base change of $\Phi$ to the fixed field of `sylowH e` — level $\top$, with $a$ at a prime $\mathfrak{P}$ the Satake power of $(a,b)$ below $\mathfrak{P}$ for the inertia degree and $b$ at $\mathfrak{P}$ the corresponding power of $b$ below — agrees with the lift-trace seed `liftTraceSeed e (sylowH e)`, whose entries at $w$ are the trace and determinant of the explicit $\mathrm{GL}_2(\mathbb{Z}[\sqrt{-2}])$-lift of $e(\mathrm{Frob}_w)$, outside some finite set of height-one primes. Second, for both $i \in \{0,1\}$ the cuspidality predicate of `viaGeneralCuspNotion` over $\mathbb{Q}$ holds for $\Phi$ when $i = 0$ and for the twist of $\Phi$ by `chiNegThreeWeight` (multiplying $a$ by $\chi_{-3}$ and $b$ by $\chi_{-3}^2$) when $i = 1$; that predicate requires a smooth realization at the general production pins of the complexified central datum which is genuine, has the weight-one archimedean character and is holomorphic at each real place, together with $b_v = \chi_{-3}(\mathrm{N}v)$ for all but finitely many $v$.
--
--   This is the octahedral case of the Langlands–Tunnell theorem over $\mathbb{Q}$, stated at the grain at which the non-normal cubic base change sees the eigenvalue table: the weight-one cuspidal pair produced over $\mathbb{Q}$ is pinned down by the requirement that its base change to the cubic resolvent field reproduce the explicit lift-trace table of $e$. It feeds [`LanglandsTunnell.exists_liftValued_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_liftValued_isCusp_pair_of_detDictionaryRow_of_coversModCentre), the step that supplies the mod-$3$ modularity input to the Frey-curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_P52Interface
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : LanglandsTunnell.DetDictionaryRow e)
    (c₂ u₂ d₂₁ d₂₂ : ℝ)
    (T₂ : Finset (AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))
    (hd₂ : d₂₁ < d₂₂)
    (hcov₂ : AutomorphicForm.SiegelCovering.CoversModCentre
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      (⋃ x ∈ T₂, (· * x) ''
        AutomorphicForm.WindowedSiegel.centreCutSiegelSet
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) c₂ u₂ d₂₁ d₂₂))
    (hc₂ : 0 < c₂)
    (hd₂₁ : 0 < d₂₁)
    (c₃ u₃ d₃₁ d₃₂ : ℝ)
    (T₃ : Finset (AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))))
    (hd₃ : d₃₁ < d₃₂)
    (hcov₃ : AutomorphicForm.SiegelCovering.CoversModCentre
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
      (⋃ x ∈ T₃, (· * x) ''
        AutomorphicForm.WindowedSiegel.centreCutSiegelSet
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) c₃ u₃ d₃₁ d₃₂))
    (hc₃ : 0 < c₃)
    (hd₃₁ : 0 < d₃₁)
    (c₆ u₆ d₆₁ d₆₂ : ℝ)
    (T₆ : Finset (AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : AutomorphicForm.SiegelCovering.CoversModCentre
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (⋃ x ∈ T₆, (· * x) ''
        AutomorphicForm.WindowedSiegel.centreCutSiegelSet
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₆₁ d₆₂))
    (hc₆ : 0 < c₆)
    (hd₆₁ : 0 < d₆₁) :
    ∃ Φ : AutomorphicForm.HeckeEigensystem ℚ (Zsqrtd (-2)),
      AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite
        (AutomorphicForm.formalBaseChange ℚ
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ)
        (LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.sylowH e)) ∧
      ∀ i : Fin 2, AutomorphicForm.viaGeneralCuspNotion.IsCusp ℚ
        (if i = 0 then Φ else Φ.twist LanglandsTunnell.chiNegThreeWeight) := by sorry
