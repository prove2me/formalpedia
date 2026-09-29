-- Prove2me | Theorems.Thm_LanglandsTunnell_not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
-- name    : LanglandsTunnell.not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/398e98f9-a335-5c7b-9fd6-8a9e7dce09dc
-- title:
--   No self-twist by the determinant sign character
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, equipped with a group isomorphism $e$ from $\mathrm{Gal}(L/\mathbb{Q})$ onto $GL_2(\mathbb{Z}/3)$, and let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, i.e. a nonzero level ideal of $\mathcal{O}_{\mathbb{Q}}$ together with functions $a,b$ on the height-one primes of $\mathcal{O}_{\mathbb{Q}}$. Write $\mathrm{detKer}\,e$ for the kernel of $\det\circ e$ and $\mathrm{quatH}\,e$ for its intersection with `sylowH e` (the subgroup of $\gamma$ whose image $e\gamma$ admits a lift in `P16`), and let $K_1,K_2$ be their fixed subfields. The first hypothesis says that the iterated formal base change of $\Phi$ from $\mathbb{Q}$ to $K_1$ and then to $K_2$ — whose Satake data at a prime $\mathfrak{P}$ are obtained from those below it by the Satake recursion in the residue degree — agrees, outside some finite set of primes of $\mathcal{O}_{K_2}$, in both $a$ and $b$ with the image under $\mathbb{Z}[\sqrt{-2}]\to\mathbb{C}$, $\sqrt{-2}\mapsto\sqrt{2}\,i$, of the lift-trace seed `P2.liftTraceSeed e (quatH e)`, whose $a$ and $b$ at $w$ are the trace and determinant of a chosen $\mathbb{Z}[\sqrt{-2}]$-lift of $e$ applied to the seed Frobenius at $w$. Further, $S_0$ is a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ and $\chi$ a complex-valued function on primes such that for every $v\notin S_0$, every maximal ideal $Q$ of $\mathcal{O}_L$ lying under the prime $v$ and every arithmetic Frobenius $\sigma$ at $Q$, one has $\chi(v)=1$ exactly when $\sigma\in\mathrm{detKer}\,e$ and $\chi(v)=-1$ exactly when $\sigma\notin\mathrm{detKer}\,e$. The conclusion is that $\Phi$ does not agree away from a finite set of primes with its twist by $\chi$, that is, there is no finite $S$ with $a_v=\chi(v)a_v$ and $b_v=\chi(v)^2b_v$ for all $v\notin S$.
--
--   This is the 'no self-twist by the quadratic determinant character' guard in the octahedral (Langlands–Tunnell) part of the argument: an eigensystem whose base change to the fixed field of the quaternion subgroup matches the explicit $\mathbb{Z}[\sqrt{-2}]$ lift-trace seed cannot be isomorphic, away from finitely many primes, to its twist by the sign of $\det e(\mathrm{Frob})$. It feeds the existence statement [`LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH`](thm.html#LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH.lean

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

theorem LanglandsTunnell.not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : HeckeEigensystem ℚ ℂ)
    (h₆seed : (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e))
          (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).AgreesAwayFromFinite
        ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo))
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)

    (hdet : ∀ v ∉ S₀, ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal →
        IsArithFrobAt (𝓞 ℚ) σ Q → (χ v = 1 ↔ σ ∈ detKer e) ∧ (χ v = -1 ↔ σ ∉ detKer e)) :
    ¬ Φ.AgreesAwayFromFinite (Φ.twist χ) := by sorry
