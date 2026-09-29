-- Prove2me | Theorems.Thm_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
-- name    : LanglandsTunnell.agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/154bcca5-8e54-54c6-9e2f-007236cd243c
-- title:
--   Quadratic base-change fibre over the cubic resolvent
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, equipped with a group isomorphism $e : \mathrm{Gal}(L/\mathbb{Q}) \cong \mathrm{GL}_2(\mathbb{Z}/3)$ satisfying `DetDictionaryRow`: for every prime $\ell \neq 3$ and every prime ideal $Q$ of $\mathcal{O}_L$ over $\ell\mathbb{Z}$ with finite residue ring and trivial inertia subgroup in $\mathrm{Gal}(L/\mathbb{Q})$, the determinant of the matrix $e(\mathrm{Frob}_Q)$ equals $\ell$ in $\mathbb{Z}/3$. Write $E_3$ for the fixed field of `sylowH e` (those $\gamma$ whose matrix $e\gamma$ is the reduction of a member of the explicit matrix set `P16`) and $E_6$ for the fixed field of `quatH e`, the intersection of `sylowH e` with the kernel of $\det \circ e$. Fix reals $c_3,u_3,d_{31},d_{32}$ with $d_{31}<d_{32}$ and a finite set $T_3$ of elements of $\mathrm{GL}_2(\mathbb{A}_{E_3})$, and likewise $c_6,u_6,d_{61},d_{62}$ with $d_{61}<d_{62}$ and $T_6 \subset \mathrm{GL}_2(\mathbb{A}_{E_6})$; let $D_j$ be the union over $x \in T_j$ of the right translates by $x$ of the centre-cut Siegel set of $E_j$ with those parameters (finite part integral, local height at least $c_j$, window $\mathrm{xWindowSq} \le u_j^2$, archimedean determinant norms in $[d_{j1},d_{j2}]$ at every infinite place), and assume each $D_j$ covers modulo global points and the centre, i.e. every $g \in \mathrm{GL}_2(\mathbb{A}_{E_j})$ admits $\gamma \in \mathrm{GL}_2(E_j)$ and a central adelic scalar $z$ with $\gamma g z \in D_j$. Let $\Phi_c, \Phi_c'$ be complex Hecke eigensystems over $E_3$ (a nonzero level ideal together with Satake data $a,b$ indexed by the height-one spectrum) and $\Phi_6$ one over $E_6$, each assumed arithmetically genuinely cusp-realizable at the production pins of its field built from $D_j$, the level subgroups $N \mapsto \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}$ and the adelic box (that is, the eigensystem with $b$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$ admits a genuine smooth cusp realization there). Assume finally that the formal base changes to $E_6$ of $\Phi_c$ and of $\Phi_c'$ — with level $\top$, $a_{\mathfrak{P}} = \mathrm{satakePow}_f(a_{\mathfrak{p}},b_{\mathfrak{p}})$ and $b_{\mathfrak{P}} = b_{\mathfrak{p}}^{f}$ for $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_{E_3}$ and $f$ the inertia degree — each agree with $\Phi_6$ at all but finitely many primes. Then either $\Phi_c'$ agrees with $\Phi_c$ at all but finitely many primes, or it so agrees with the twist of $\Phi_c$ ($a_v \mapsto \chi_v a_v$, $b_v \mapsto \chi_v^2 b_v$, same level) by the character $\chi_v = \iota(\chi_{-3}(p)^{f})$, where $\mathfrak{p} = v \cap \mathbb{Z}$ corresponds to the rational prime $p$, $f$ is the inertia degree of $v$ over it, $\chi_{-3}(p)$ is $1$, $-1$ or $0$ according as $p \equiv 1, 2, 0 \pmod 3$, and $\iota : \mathbb{Z}[\sqrt{-2}] \to \mathbb{C}$ sends $\sqrt{-2}$ to $\sqrt{2}\,i$.
--
--   This is Tunnell's lemma on the fibre of quadratic base change, at the level of Hecke-eigenvalue tables: two genuinely cusp-realizable eigensystems over the cubic resolvent $E_3$ with the same formal base change to $E_6$ differ at most by the quadratic character attached to $\mathbb{Q}(\sqrt{-3})$ pulled back to $E_3$. It is obtained from the general two-field statement [`AutomorphicForm.HeckeEigensystem.agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre`](thm.html#AutomorphicForm.HeckeEigensystem.agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre) and feeds the construction of a cuspidal pair in [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH.lean

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_BcWeight
import Definitions.Def_LanglandsTunnell_P52Interface
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

theorem LanglandsTunnell.agreesAwayFromFinite_or_twist_bcWeight_of_formalBaseChange_agree_sylowH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : DetDictionaryRow e)
    (c₃ u₃ d₃₁ d₃₂ : ℝ) (T₃ : Finset (AdelicGL2 (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e))))
    (c₆ u₆ d₆₁ d₆₂ : ℝ) (T₆ : Finset (AdelicGL2 (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e))))
    (Φc Φc' : HeckeEigensystem ↥(fixFld (sylowH e)) ℂ) (Φ₆ : HeckeEigensystem ↥(fixFld (quatH e)) ℂ)
    (hΦc : IsArithGenuineCuspRealizable ↥(fixFld (sylowH e))
      (productionPinsOf ↥(fixFld (sylowH e))
        (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂)
        (fun N => levelOne (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (sylowH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) v) (adelicBox ↥(fixFld (sylowH e)))) Φc)
    (hΦc' : IsArithGenuineCuspRealizable ↥(fixFld (sylowH e))
      (productionPinsOf ↥(fixFld (sylowH e))
        (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂)
        (fun N => levelOne (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (sylowH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (sylowH e))) ↥(fixFld (sylowH e)) v) (adelicBox ↥(fixFld (sylowH e)))) Φc')
    (hc₆ : IsArithGenuineCuspRealizable ↥(fixFld (quatH e))
      (productionPinsOf ↥(fixFld (quatH e))
        (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂)
        (fun N => levelOne (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (quatH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) v) (adelicBox ↥(fixFld (quatH e)))) Φ₆)
    (hd₃ : d₃₁ < d₃₂)
    (hcov₃ : CoversModCentre ↥(fixFld (sylowH e))
      (⋃ x ∈ T₃, (· * x) '' centreCutSiegelSet ↥(fixFld (sylowH e)) c₃ u₃ d₃₁ d₃₂))
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : CoversModCentre ↥(fixFld (quatH e))
      (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂))
    (hBC : (formalBaseChange ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) Φc).AgreesAwayFromFinite Φ₆)
    (hBC' : (formalBaseChange ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) Φc').AgreesAwayFromFinite Φ₆) :
    Φc'.AgreesAwayFromFinite Φc ∨
      Φc'.AgreesAwayFromFinite
        (Φc.twist (bcWeight ℚ ↥(fixFld (sylowH e)) (fun v => iotaZsqrtdNegTwo (chiNegThreeWeight v)))) := by sorry
