-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
-- name    : LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/55a02bd6-0890-50a1-a5f4-1ec816271993
-- title:
--   Seed table over the cubic resolvent as a theta table
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, equipped with a group isomorphism $e\colon \mathrm{Gal}(L/\mathbb{Q}) \xrightarrow{\sim} \mathrm{GL}_2(\mathbb{Z}/3)$ satisfying `DetDictionaryRow e`: for every prime $\ell \neq 3$ and every prime $Q$ of $\mathcal{O}_L$ lying over $\ell$ with finite residue field and trivial inertia subgroup in $\mathrm{Gal}(L/\mathbb{Q})$, $\det e(\mathrm{Frob}_Q) = \ell$ in $\mathbb{Z}/3$. Write $E =$ `fixFld (sylowH e)`, the subfield of $L$ fixed by the subgroup of those $\gamma$ for which $e(\gamma)$ is the mod $3$ reduction of a matrix in the set $P16$ over $\mathbb{Z}[\sqrt{-2}]$, and write $a_v, b_v \in \mathbb{Z}[\sqrt{-2}]$ for the trace and determinant of the chosen lift `liftOf` of $e(\mathrm{seedFrob})$ at a finite place $v$ of $E$, i.e. the Hecke eigensystem `P2.liftTraceSeed e (sylowH e)`; let $\iota\colon \mathbb{Z}[\sqrt{-2}] \to \mathbb{C}$ be the ring homomorphism sending $\sqrt{-2}$ to $\sqrt{2}\,i$. The assertion is the existence of a type $M$ with the structure of a number field and of an $E$-algebra with $[M:E] = 2$, of a function $\psi$ from the finite places of $\mathcal{O}_M$ to $\mathbb{C}^\times$, and of a non-zero ideal $\mathfrak{f}$ of $\mathcal{O}_M$, such that: (1) for every non-zero $\alpha \in \mathcal{O}_M$ with $\alpha - 1 \in \mathfrak{f}$ and $\tau(\alpha) > 0$ for all real embeddings $\tau$ of $M$, the symbol $\prod_{\mathfrak{P}} \psi(\mathfrak{P})^{\mathrm{ord}_{\mathfrak{P}}((\alpha))}$ equals $1$; (2) outside any finite set $S$ of places of $E$ there is a place $v \notin S$ carrying two distinct primes $\mathfrak{P}_1 \neq \mathfrak{P}_2$ of $\mathcal{O}_M$ with $\mathfrak{P}_i$ under $E$ equal to $v$ and $\psi(\mathfrak{P}_1) \neq \psi(\mathfrak{P}_2)$; (3) for some finite set $S$ of places of $E$ and all $v \notin S$: whenever $\mathfrak{P}_1 \neq \mathfrak{P}_2$ both lie under $v$ one has $\iota(a_v) = \psi(\mathfrak{P}_1) + \psi(\mathfrak{P}_2)$ and $\iota(b_v) = \psi(\mathfrak{P}_1)\psi(\mathfrak{P}_2)$, while for $\mathfrak{P}$ over $v$ of inertia degree $2$ one has $a_v = 0$ and $\iota(b_v) = -\psi(\mathfrak{P})$; and (4) for some finite set $S$ of places of $E$ and all $v \notin S$, $b_v$ is the image in $\mathbb{Z}[\sqrt{-2}]$ of $\chi_{-3}(N v)$, which is $1$, $-1$ or $0$ according as the absolute norm of $v$ is $1$, $2$ or $0$ modulo $3$.
--
--   This is the dictionary, in the octahedral case of Langlands–Tunnell, between the Artin seed table of $e$ read over the cubic resolvent field $E$ fixed by the chosen $2$-group `sylowH e` and the theta table attached to a character of a quadratic extension $M$ of $E$; clauses (1)–(4) are precisely the input required by the theta-realisation step. It feeds the construction of a cusp form agreeing with the seed table, used downstream in [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow.lean

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_NarrowRayClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open IsDedekindDomain
open AutomorphicForm
open Deep.NTSupply
open scoped nonZeroDivisors

theorem LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (hdet : DetDictionaryRow e) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ↥(fixFld (sylowH e)) M),
      Module.finrank ↥(fixFld (sylowH e)) M = 2 ∧
      ∃ (ψ : HeightOneSpectrum (𝓞 M) → ℂˣ) (𝔣 : Ideal (𝓞 M)), 𝔣 ≠ ⊥ ∧
      (∀ α : 𝓞 M, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : M →+* ℝ, 0 < τ (algebraMap (𝓞 M) M α)) →
      raySymbol M ψ ((Ideal.span {α} : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M) = 1) ∧
      (∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∃ v ∉ S, ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (sylowH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (sylowH e))) = v ∧ ψ 𝔓₁ ≠ ψ 𝔓₂) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 ↥(fixFld (sylowH e))) = v →
          𝔓₂.under (𝓞 ↥(fixFld (sylowH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧
            iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 M), 𝔓.under (𝓞 ↥(fixFld (sylowH e))) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (sylowH e)).a v = 0 ∧ iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) =
            -(ψ 𝔓 : ℂ))) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∀ v ∉ S,
      (P2.liftTraceSeed e (sylowH e)).b v =
          ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) := by sorry
