-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow
-- name    : LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/f27205ad-8f5b-5827-b5b0-6d4507f3dff3
-- title:
--   Ray class character realising the Q₈ seed table
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism from $\operatorname{Gal}(L/\mathbb{Q})$ onto $\mathrm{GL}_2(\mathbb{Z}/3)$ satisfying the determinant dictionary `DetDictionaryRow e`: for every prime $\ell \neq 3$ and every prime ideal $Q$ of $\mathcal{O}_L$ lying over $\ell\mathbb{Z}$ with finite residue ring and with trivial inertia subgroup in $\operatorname{Gal}(L/\mathbb{Q})$, the determinant of $e(\mathrm{Frob}_Q)$ equals $\ell \bmod 3$. Write $H =$ `quatH e` for the intersection of `sylowH e` (the $\gamma$ whose image $e(\gamma)$ is the mod $3$ reduction of a matrix in the explicit $16$-element set $P16$ over $\mathbb{Z}[\sqrt{-2}]$) with the kernel of $\det \circ e$, and $E =$ `fixFld (quatH e)` for its fixed field inside $L$. Let $a, b \colon v \mapsto \operatorname{tr} \mathrm{liftOf}(e(\mathrm{seedFrob}))$, $\det \mathrm{liftOf}(e(\mathrm{seedFrob}))$ be the two coefficient functions of the Hecke eigensystem `P2.liftTraceSeed e (quatH e)` on the finite places of $E$, with values in $\mathbb{Z}[\sqrt{-2}]$, and let $\iota =$ `iotaZsqrtdNegTwo` be the ring homomorphism $\mathbb{Z}[\sqrt{-2}] \to \mathbb{C}$ sending $\sqrt{-2}$ to $\sqrt{2}\,i$. The assertion is the existence of a number field $M$ equipped with an $E$-algebra structure with $\operatorname{finrank}_E M = 2$, a function $\psi$ from the finite places of $M$ to $\mathbb{C}^\times$, and a non-zero ideal $\mathfrak{f}$ of $\mathcal{O}_M$, such that: (i) for every non-zero $\alpha \in \mathcal{O}_M$ with $\alpha - 1 \in \mathfrak{f}$ and $\tau(\alpha) > 0$ for all real embeddings $\tau$ of $M$, the symbol $\prod_{\mathfrak{P}} \psi(\mathfrak{P})^{\operatorname{count}_{\mathfrak{P}}(\alpha \mathcal{O}_M)}$ equals $1$; (ii) outside any given finite set of finite places of $E$ there is a place $v$ with two distinct primes $\mathfrak{P}_1 \neq \mathfrak{P}_2$ of $\mathcal{O}_M$ both lying under $v$ and $\psi(\mathfrak{P}_1) \neq \psi(\mathfrak{P}_2)$; (iii) for some finite set $S$ of finite places of $E$ and all $v \notin S$: whenever $\mathfrak{P}_1 \neq \mathfrak{P}_2$ both lie under $v$ one has $\iota(a_v) = \psi(\mathfrak{P}_1) + \psi(\mathfrak{P}_2)$ and $\iota(b_v) = \psi(\mathfrak{P}_1)\psi(\mathfrak{P}_2)$, and whenever $\mathfrak{P}$ lies under $v$ with `inertiaDeg'` equal to $2$ one has $a_v = 0$ and $\iota(b_v) = -\psi(\mathfrak{P})$; and (iv) for some finite set $S$ of finite places of $E$ and all $v \notin S$, $b_v$ is the image in $\mathbb{Z}[\sqrt{-2}]$ of $\chi_{-3}(N v)$, where $\chi_{-3}(n)$ is $1$, $-1$ or $0$ according as $n \equiv 1$, $2$ or $0 \bmod 3$ and $N v$ is the absolute norm of $v$.
--
--   This is the dictionary step in the octahedral case of Langlands–Tunnell: over the fixed field of the quaternionic subgroup cut out by $e$, the seed table $(a_v, b_v)$ attached to the explicit $\mathbb{Z}[\sqrt{-2}]$-lifts of Frobenius is matched with the table of a character $\psi$ of places of a quadratic extension $M$ of that field, whose ray behaviour, splitting non-triviality, trace–norm identities and determinant row are packaged as clauses (i)–(iv). These clauses are exactly the input of the subsequent theta-series realisation, and the theorem is used by [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow.lean

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

theorem LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (hdet : DetDictionaryRow e) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ↥(fixFld (quatH e)) M),
      Module.finrank ↥(fixFld (quatH e)) M = 2 ∧
      ∃ (ψ : HeightOneSpectrum (𝓞 M) → ℂˣ) (𝔣 : Ideal (𝓞 M)), 𝔣 ≠ ⊥ ∧
      (∀ α : 𝓞 M, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : M →+* ℝ, 0 < τ (algebraMap (𝓞 M) M α)) →
      raySymbol M ψ ((Ideal.span {α} : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M) = 1) ∧
      (∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∃ v ∉ S, ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v ∧ ψ 𝔓₁ ≠ ψ 𝔓₂) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v →
          𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧
            iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 M), 𝔓.under (𝓞 ↥(fixFld (quatH e))) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (quatH e)).a v = 0 ∧ iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) = -(ψ 𝔓 : ℂ))) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∀ v ∉ S,
      (P2.liftTraceSeed e (quatH e)).b v = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) := by sorry
