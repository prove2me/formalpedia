-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_claim_B_1_2
-- name    : ObfImpossibility.PseudoOracle.claim_B_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:26.935986+00:00
-- url     : https://prove2.me/theorems/49d3a308-626a-4752-a2dd-631e6d867fe9
-- title:
--   Claim B.1.2, p. A:44 — the $G$ admitting a good $S_G\subseteq S$ number at most $B\cdot2^{-cK^{1-7\delta}}$
-- statement:
--   There is $\delta_0>0$ such that for every $0<\delta\le\delta_0$ there are $c>0$ and $K_0$ with the following property. Let $K\ge K_0$, $L\ge K^2$, let $D$ make at most $K^\delta$ oracle queries, and let $S\subseteq[K]$ have $\lfloor K^{1-5\delta}\rfloor$ elements. Let $B$ be the number of injective functions $[K]\to[L]$. Then the number of injective $G:[K]\to[L]$ for which some $S_G$ satisfies Properties (1)–(3) of Claim B.1.1 (with this $S$ and $\gamma=K^{-3\delta}$) is at most
--   $$B\cdot 2^{-c\,K^{1-7\delta}} .$$
--
--   The paper states this as a description length: every such $G$ "can be uniquely described by $(\log B)-\Omega(K^{1-7\delta})$ bits given $D$". A set whose members each have a distinct description of at most $m$ bits has at most $2^{m+1}$ members, so the counting form is equivalent up to the constant $c$. It is the compression step of the Gennaro–Trevisan style argument: the set $S_G$, the values of $G$ off $S_G$, one sign bit and the image $T=G(S_G)$, which inequality (9) confines to a small fraction of the candidates, determine $G$.
--
--   **Formalization Note** The paper states the claim for the set $\mathcal G'$ of Claim B.1.1; since every $G\in\mathcal G'$ admits a good $S_G\subseteq S$, the bound here covers $\mathcal G'$. The existence of $\delta_0$ renders the paper's "for a sufficiently small $\delta$, whose value is implicit in the proof"; $c$ depends only on $\delta$ and $K_0$ only on $\delta$ and $c$. Property (1) is read as $|S_G|\ge(1-\gamma)|S|$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:44, Appendix B, Claim B.1.2 (counting form; proof on pp. A:44–A:45)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

open Classical in
/-- Claim B.1.2, p. A:44, counting form: for every sufficiently small `δ > 0` there is
`c > 0` such that for all large `K`, all `L ≥ K²`, every `D` making at most `K^δ` queries
and every `S ⊆ [K]` of size `⌊K^{1-5δ}⌋`, the injective `G : [K] → [L]` that admit a set
`S_G ⊆ S` with Properties (1)–(3) of Claim B.1.1 number at most `B · 2^{-c K^{1-7δ}}`,
where `B` is the number of injective functions `[K] → [L]` ("each such `G` is described by
`log B - Ω(K^{1-7δ})` bits given `D`"). -/
theorem claim_B_1_2 :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ,
      ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
        ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
          ∀ S : Finset (Fin K), S.card = ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ →
            ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
                ∃ SG : Finset (Fin K), GoodSubset D δ S G SG).card : ℝ) ≤
              (Fintype.card (Fin K ↪ Fin L) : ℝ) *
                (2 : ℝ) ^ (-(c * (K : ℝ) ^ (1 - 7 * δ))) := by sorry

end ObfImpossibility.PseudoOracle
