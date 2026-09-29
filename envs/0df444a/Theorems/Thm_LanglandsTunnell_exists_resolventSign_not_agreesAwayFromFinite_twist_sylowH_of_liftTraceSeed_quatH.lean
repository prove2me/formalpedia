-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
-- name    : LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/45d0d24f-89b7-554a-8319-6c698c869c46
-- title:
--   Resolvent sign character and non-self-twist guard for GL₂(𝔽₃) towers
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism from $\mathrm{Gal}(L/\mathbb{Q})$ onto $GL_2(\mathbb{Z}/3)$; write $\mathrm{detKer}\,e$ for the kernel of $\det\circ e$, $\mathrm{sylowH}\,e$ for the subgroup of those $\gamma$ whose matrix $e\gamma$ is the reduction mod $3$ of an element of the matrix set `P16` over $\mathbb{Z}\sqrt{-2}$, and $\mathrm{quatH}\,e=\mathrm{sylowH}\,e\cap\mathrm{detKer}\,e$; `fixFld` of a subgroup is its fixed subfield. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, that is, a nonzero level ideal together with functions $a,b$ on the height-one primes of $\mathbb{Z}$. Assume that the formal base change of $\Phi$ from $\mathbb{Q}$ to the fixed field of $\mathrm{detKer}\,e$ and then to the fixed field of $\mathrm{quatH}\,e$ — each step taking level $\top$, $a$ at $\mathfrak{P}$ to the Satake power $\mathrm{satakePow}$ of the inertia degree of $\mathfrak{P}$ applied to the values below, and $b$ to the corresponding power of $b$ — agrees, outside some finite set of primes, with the image under $\mathbb{Z}\sqrt{-2}\to\mathbb{C}$, $\sqrt{-2}\mapsto\sqrt{2}\,i$, of the lift-trace seed `P2.liftTraceSeed` of $\mathrm{quatH}\,e$, whose $a$- and $b$-values at $w$ are the trace and determinant of a chosen lift over $\mathbb{Z}\sqrt{-2}$ of $e(\mathrm{seedFrob}\,w)$. Then there are a finite set $S_0$ of height-one primes of $\mathbb{Z}$ and a function $\chi$ on the height-one primes of $\mathbb{Z}$ with complex values such that: $\chi(v)^2=1$ for all $v\notin S_0$; for all $v\notin S_0$, $\chi(v)=1$ if and only if no prime $\mathfrak{P}$ of the ring of integers of the fixed field of $\mathrm{sylowH}\,e$ lying under $v$ has inertia degree $2$; and $\Phi$ does not agree away from a finite set of primes with its twist by $\chi$, the eigensystem with the same level and with values $\chi(v)a(v)$ and $\chi(v)^2b(v)$.
--
--   This packages the two pieces of input required for the non-normal cubic base-change step in the Langlands–Tunnell argument for a $GL_2(\mathbb{F}_3)$-tower: the quadratic resolvent sign character of the tower, characterised by inertia degrees in the cubic subfield cut out by the Sylow subgroup, together with the guarantee that the eigensystem $\Phi$ is not isomorphic to its own twist by that character. It is used by [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH.lean

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (h₆seed : (AutomorphicForm.formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
          (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) Φ)).AgreesAwayFromFinite
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map AutomorphicForm.iotaZsqrtdNegTwo)) :
    ∃ (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (χ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → ℂ),
      (∀ v ∉ S₀, χ v * χ v = 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S₀ →
        (χ v = 1 ↔ ∀ 𝔓 : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
          𝔓.under (NumberField.RingOfIntegers ℚ) = v →
            (𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2)) ∧
      ¬ Φ.AgreesAwayFromFinite (Φ.twist χ) := by sorry
