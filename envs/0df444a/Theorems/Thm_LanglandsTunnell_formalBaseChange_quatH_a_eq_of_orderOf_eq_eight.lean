-- Prove2me | Theorems.Thm_LanglandsTunnell_formalBaseChange_quatH_a_eq_of_orderOf_eq_eight
-- name    : LanglandsTunnell.formalBaseChange_quatH_a_eq_of_orderOf_eq_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/6291ac75-a2c8-5db3-8d44-338a0ff7d64c
-- title:
--   Quaternion-layer formal base change at Frobenius of order eight
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism $\mathrm{Gal}(L/\mathbb{Q}) \cong \mathrm{GL}_2(\mathbb{Z}/3)$. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$, that is, a nonzero level ideal together with two functions $a,b$ on the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$. Fix a height one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, an ideal $Q$ of $\mathcal{O}_L$ and $\sigma \in \mathrm{Gal}(L/\mathbb{Q})$, and assume: $Q$ is maximal, $Q$ contracts to $v$, the inertia subgroup of $Q$ in $\mathrm{Gal}(L/\mathbb{Q})$ is trivial, $\sigma$ is an arithmetic Frobenius at $Q$ over $\mathcal{O}_{\mathbb{Q}}$, and $e(\sigma)$ has order $8$. Write $E$ for the fixed field of `detKer e`, the kernel of $\det \circ e$, and $E_6$ for the fixed field of `quatH e` $=$ `sylowH e` $\sqcap$ `detKer e`, where `sylowH e` consists of those $\gamma$ whose matrix $e(\gamma)$ is the reduction of a member of the set $P16$. Let $w$ be a height one prime of $\mathcal{O}_{E_6}$ contracting to $v$. Then, for the two-step formal base change of $\Phi$ from $\mathbb{Q}$ to $E$ and then to $E_6$ (whose Satake data at a prime $\mathfrak{P}$ are $\mathrm{satakePow}$ of the inertia degree applied to the data below $\mathfrak{P}$, and the lower $b$ raised to that degree), the $a$-value at $w$ is $\Phi.a(v)^2 - 2\,\Phi.b(v)$ and the $b$-value at $w$ is $\Phi.b(v)^2$.
--
--   This is the arithmetic bookkeeping that reads off the Satake parameters of the formal base change to the quaternionic layer $E_6$ of the $\mathrm{GL}_2(\mathbb{F}_3)$-tower at a prime whose Frobenius image has order $8$: the answer is the degree-two Satake power, so $v$ behaves as if inert of residue degree $2$ in $E_6$. It is used in the Langlands–Tunnell part of the argument, in the verification that a twisted lift cannot agree with the relevant eigensystem away from a finite set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_formalBaseChange_quatH_a_eq_of_orderOf_eq_eight.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

theorem LanglandsTunnell.formalBaseChange_quatH_a_eq_of_orderOf_eq_eight
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (Φ : HeckeEigensystem ℚ ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L)
    (hQ : Q.IsMaximal) (hQv : Q.under (𝓞 ℚ) = v.asIdeal) (hunr : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hσ : IsArithFrobAt (𝓞 ℚ) σ Q) (h8 : orderOf (e σ) = 8)
    (w : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))) (hw : w.under (𝓞 ℚ) = v) :
    (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).a w
        = Φ.a v ^ 2 - 2 * Φ.b v ∧
      (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).b w
        = Φ.b v ^ 2 := by sorry
