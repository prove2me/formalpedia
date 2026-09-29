-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
-- name    : LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/41d83c70-3512-5bdc-947b-718c85b2032a
-- title:
--   Level of the local standard character equals the exponent of the different
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, with $K_v$ the $v$-adic completion of $K$. Let $\psi_K$ denote the standard additive character `stdAddChar K` of the adele ring of $K$, namely the character $\psi_K$ attached to the adelic trace data of $K$, and let $\iota_v \colon K_v \to \mathbb{A}_K$ be the additive map `adeleSingleAt K v` sending $x$ to the adele whose infinite part is $0$ and whose finite part is the finite adele with component $x$ at $v$ and $0$ elsewhere. The local character at $v$ is $\psi_{K,v} = \psi_K \circ \iota_v$, an additive character of $K_v$ with values in $\mathbb{C}$, and its level `addCharLevel` is defined as the supremum, taken in $\mathbb{Z}$ (so equal to $0$ by convention when the set is empty or unbounded above), of the set of integers $n$ such that $\psi_{K,v}(x) = 1$ for every $x \in K_v$ with $\mathrm{v}(x) \le \exp(n)$ in the value group $\mathbb{Z}^{\text{multiplicative}} \cup \{0\}$. The assertion is that this level equals `FractionalIdeal.count K v` of the different ideal $\mathfrak{d}_{\mathcal{O}_K/\mathbb{Z}}$ of $\mathcal{O}_K$ over $\mathbb{Z}$, regarded as a fractional ideal of $K$, that is, the exponent of $v$ in the factorisation of the different.
--
--   This identifies the conductor (level) of the local component at a finite place of the standard adelic additive character with the local exponent of the different $\mathfrak{d}_{K/\mathbb{Q}}$, the normalisation underlying the local theory of Tate's thesis: the finite part of $\psi_K$ is trivial on the integral adeles precisely along the inverse different. It is used in the computation of local constants and local integrals at finite places, and is invoked in the Rankin–Selberg and class-sum growth estimates downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped nonZeroDivisors

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    addCharLevel (psiLocal K v)
      = FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by sorry
