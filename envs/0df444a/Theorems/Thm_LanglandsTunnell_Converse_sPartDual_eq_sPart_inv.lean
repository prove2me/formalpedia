-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv
-- name    : LanglandsTunnell.Converse.sPartDual_eq_sPart_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/5083b3c9-1a7a-5154-9885-b2f95b8773f5
-- title:
--   Dual S-part series equals the S-part series of μ⁻¹
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, let $Ad \colon (S \to \mathbb{Z}) \to \mathbb{C}$ be a family of complex coefficients indexed by the integer vectors on $S$, let $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a monoid homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$, and let $s \in \mathbb{C}$. By definition, `sPart K S Ad μ s` is the unconditional sum $\sum_{n \colon S \to \mathbb{Z}} Ad(n) \prod_{v \in S} \bigl(\mu(\varpi_v)\, N(v)^{1/2 - s}\bigr)^{n_v}$, where $\varpi_v$ denotes `uniformizerIdele K v`, the idele obtained from a chosen uniformizer unit at $v$ by the inclusion of the finite part, $N(v)$ is the absolute norm of the ideal $v$, and the complex power is the principal one; `sPartDual K S Ad μ s` is the same expression with $\mu(\varpi_v)^{-1}$ in place of $\mu(\varpi_v)$. The assertion is that `sPartDual K S Ad μ s` equals `sPart K S Ad μ⁻¹ s`, the character $\mu^{-1}$ being the pointwise inverse of $\mu$. No hypotheses beyond the data are imposed.
--
--   This records that the dual $S$-part series is not a new object: it is the $S$-part series attached to the inverse idele character, so every identity proved for `sPart` transfers to `sPartDual`. It is used in the converse-theorem input for Langlands–Tunnell, in the construction of nice pinned data and in the shift property [`LanglandsTunnell.Converse.isNicePinned_sPart_shift`](thm.html#LanglandsTunnell.Converse.isNicePinned_sPart_shift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.Converse.sPartDual_eq_sPart_inv (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) :
    sPartDual K S Ad μ s = sPart K S Ad μ⁻¹ s := by sorry
