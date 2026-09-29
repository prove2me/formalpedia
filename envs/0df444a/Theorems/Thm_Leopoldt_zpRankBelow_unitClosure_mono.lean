-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_mono
-- name    : Leopoldt.zpRankBelow_unitClosure_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-09T15:02:27.584397+00:00
-- url     : https://prove2.me/theorems/01e427bb-d87c-462a-919a-eb832c83716b
-- title:
--   The $\mathbb{Z}_p$-rank of the $p$-adic closure of the units does not decrease along a finite extension
-- statement:
--   Let $p$ be a prime and let $\mathbb{K}/\mathbb{F}$ be a finite extension of number fields. Write $\bar{E}(\mathbb{L}) \subseteq U_p(\mathbb{L}) = \prod_{\wp \mid p} \mathcal{O}_\wp^{\times}$ for the $p$-adic closure of the global units of a number field $\mathbb{L}$, as in Section 1.1 of the source. Then
--
--   $$\mathbb{Z}_p\text{-rk}\,\bar{E}(\mathbb{F}) \;\le\; \mathbb{Z}_p\text{-rk}\,\bar{E}(\mathbb{K}) .$$
--
--   The reason is functoriality of the semilocal units. Every prime $\mathfrak{P} \mid p$ of $\mathbb{K}$ restricts to a prime $\wp \mid p$ of $\mathbb{F}$, and conversely every $\wp \mid p$ of $\mathbb{F}$ has at least one prime of $\mathbb{K}$ above it; the completion $\mathbb{F}_\wp$ embeds in $\mathbb{K}_\mathfrak{P}$ continuously, carrying local units to local units. Assembling these gives a continuous injective homomorphism $U_p(\mathbb{F}) \to U_p(\mathbb{K})$ which commutes with the diagonal embeddings of the global units and with $p^n$-th powers, so it carries $\bar{E}(\mathbb{F})$ into $\bar{E}(\mathbb{K})$. Any continuous injection of $\mathbb{Z}_p^{\,n}$ into $\bar{E}(\mathbb{F})$ therefore composes to one into $\bar{E}(\mathbb{K})$, and $[\mathbb{F}:\mathbb{Q}] \le [\mathbb{K}:\mathbb{Q}]$ keeps the witness within the bound carried by the definition of the rank.
--
--   This is the functorial half of Remark 1.A of the source. By itself it does **not** give Remark 1.A, since Dirichlet's rank grows along $\mathbb{K}/\mathbb{F}$ as well and the defect is the difference of the two ranks. It does settle the case where the two Dirichlet ranks agree, which is what happens for a CM field over its maximal real subfield, and it is the reusable content behind both.
--
--   **Formalization note.** The two fields are related by an `Algebra` instance with `FiniteDimensional`, exactly as in the mission's statement of Remark 1.A; no compatibility with the canonical $\mathbb{Q}$-algebra structures is imposed, and none is needed, since a field of characteristic zero admits exactly one ring homomorphism from $\mathbb{Q}$. The quantity compared is `zpRankBelow p (finrank ℚ ·) (unitClosure p ·)`, the $\mathbb{Z}_p$-rank of the definition file, whose bound argument is the degree of the field over $\mathbb{Q}$.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.3 (Plan of the proof), Remark 1 part A, p. 5. Remark 1.A asserts that a positive Leopoldt defect is inherited by finite extensions and gives as its reason: "It follows from the fact that the linear relations between Z-generators of the units of E(K_1), which arise upon p-adic completion, will be preserved under the embedding into the units E(K)." The statement below isolates exactly the mechanism named in that sentence - the embedding of the p-adically completed unit groups along a finite extension - expressed in the notation of Section 1.1, p. 3 (semilocal units U, diagonal embedding iota, p-adic closure Ebar): the Z_p-rank of Ebar does not decrease along a finite extension. Cited original for Remark 1.A: M. Laurent, Rang p-adique d'unites et action de groupes, J. reine angew. Math. 399 (1989), 81-108, https://doi.org/10.1515/crll.1989.399.81.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_unitClosure_mono (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] :
    zpRankBelow p (Module.finrank ℚ F) (unitClosure p F)
      ≤ zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := by sorry
end Leopoldt
