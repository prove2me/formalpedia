-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two
-- name    : IsIntegrallyClosed.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c4b9ab55-008f-55c4-a9df-904740c783e3
-- title:
--   Denominators outside the centre of a valuation subring
-- statement:
--   Let $B$ be a noetherian local domain that is integrally closed in its field of fractions and satisfies $\operatorname{ringKrullDim} B \le 2$, let $F$ be a field, let $\mathrm{emb} \colon B \to F$ be an injective ring homomorphism, and let $V \subseteq F$ be a valuation subring with $\mathrm{emb}(b) \in V$ for every $b \in B$. Let $P$ be an ideal of $B$ which is the centre of $V$ on $B$, in the sense that for every $b \in B$ one has $b \in P$ if and only if $\mathrm{emb}(b)$ lies in the set of non-units of $V$ (equivalently, $\mathrm{emb}(b)$ belongs to $V$ and its image in $V$ lies in the maximal ideal of $V$), and assume $P$ is not the maximal ideal of $B$. Then for every $x \in F$ lying in $V$ which is a fraction of elements of $B$, i.e. such that there exist $r_0, s_0 \in B$ with $s_0 \ne 0$ and $x \cdot \mathrm{emb}(s_0) = \mathrm{emb}(r_0)$, there exist $r, s \in B$ with $s \notin P$ and $x \cdot \mathrm{emb}(s) = \mathrm{emb}(r)$; that is, $x$ admits a representation as a fraction whose denominator lies outside the centre $P$.
--
--   This is the statement that an element of the valuation ring $V$ which is a fraction of $B$ has no pole along the centre $P$ of $V$, so that it can be written with denominator invertible at $P$; behind it lies the fact that for $\dim B \le 2$ a non-zero non-maximal centre has height one, so $B_P$ is a discrete valuation ring and the trace of $V$ on $\operatorname{Frac} B$ is $B_P$. It is used in the analysis of integral models of modular curves at $p$, to recognise germs in the image of the stalk-reading maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hdim : ringKrullDim B ≤ 2)
    {F : Type*} [Field F] (emb : B →+* F) (hemb : Function.Injective emb)
    (V : ValuationSubring F) (hBV : ∀ b : B, emb b ∈ V)
    (P : Ideal B) (hP : ∀ b : B, b ∈ P ↔ emb b ∈ V.nonunits) (hPm : P ≠ IsLocalRing.maximalIdeal B) :
    ∀ x : F, x ∈ V → (∃ r₀ s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) → ∃ r s : B, s ∉ P ∧ x * emb s = emb r := by sorry
