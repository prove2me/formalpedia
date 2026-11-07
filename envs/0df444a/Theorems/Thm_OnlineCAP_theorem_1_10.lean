-- Prove2me | Theorems.Thm_OnlineCAP_theorem_1_10
-- name    : OnlineCAP.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:14.307727+00:00
-- url     : https://prove2.me/theorems/3e7d436e-9c6e-40f2-b89b-1d1c2e3ed515
-- title:
--   Theorem 1.10 — an α-competitive algorithm for TL-rectangle hitting set gives one for OCycAP
-- statement:
--   Let $L$ be a set of links (pairs of distinct vertices) on the cycle $v_0v_1\cdots v_{n-1}v_0$ with costs $c$, let $P_L=\{p_\ell:\ell\in L\}$ with $p_{\{v_i,v_j\}}=(i,j)$ for $i<j$, and let $c'$ be costs on the plane with $c'(p_\ell)=c(\ell)$ for $\ell\in L$. Let $\alpha\in\mathbb R$.
--
--   1. If online TL-rectangle hitting set on $(P_L,c')$ has a randomized online algorithm that is $\alpha$-competitive in expectation against an oblivious adversary, then OWCycAP with cut arrivals on $(L,c)$ has one.
--   2. If it has a deterministic $\alpha$-competitive algorithm, then OWCycAP on $(L,c)$ has a deterministic $\alpha$-competitive algorithm.
--
--   With unit costs on both sides this is the unweighted statement (OCycAP).
--
--   **Formalization Note** The two cases are the flag `det`. The cycle is the standard labelled cycle; the reduction is the one of §3.1 (Proposition 3.2).
--
--   Differences from the source:
--   - generalization: if every instance of (weighted) Online TL-Hitting Set has an α-competitive algorithm, then OCycAP has one → per instance: if the TL instance (P_L, c′) produced by the reduction has one, then the cycle instance (L, c) has one; reason: the hypothesis concerns one TL instance instead of all of them, so the source's statement follows by applying it to each cycle instance
--   - generalization: non-negative costs → arbitrary real costs c (and c′ = c on the points of L); reason: the reduction preserves costs and optima exactly; with c ≥ 0 or c ≡ 1 it is the source's weighted or unweighted statement
--   - reading: α-competitive algorithm → both a randomized algorithm α-competitive in expectation against an oblivious adversary, and a deterministic α-competitive algorithm, the transfer preserving determinism; reason: §2.2 defines both ratios and the paper uses the randomized transfer for Theorem 1.3 and the deterministic one for Theorem 1.4; covering both is the strongest reading
--   - encoding: a cycle G with vertices named v₀, …, v_{n−1} in cyclic order → the standard cycle on Fin n with edges {i, i+1 mod n}; reason: every cycle on n labelled vertices is a relabelling of it, and relabelling preserves competitive ratios
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 1.10, p.5 (reduction §3.1, pp.10–11)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_cycleEnds
import Definitions.Def_OnlineCAP_cycleInstance
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_IsTLShape
import Definitions.Def_OnlineCAP_tlInstance
import Definitions.Def_OnlineCAP_linkPoint
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 1.10 (OCycAP reduces to TL-rectangle hitting set).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 1.10, p.5 (PDF
p.5): "If there is an α-competitive algorithm for (weighted) Online TL-Hitting Set, then there is an
α-competitive algorithm for (weighted) OCycAP."

Let `L` be a set of links (pairs of distinct vertices) on the standard cycle `v₀ v₁ ⋯ v_{n−1} v₀`
with costs `c`, and let `c'` be a cost function on the plane with `c'(p_ℓ) = c(ℓ)` for `ℓ ∈ L`,
where `p_ℓ = (i, j)` for `ℓ = {v_i, v_j}`, `i < j`. If the online TL-rectangle hitting set
instance on the points `P_L = {p_ℓ : ℓ ∈ L}` with costs `c'` has an online algorithm that is
`α`-competitive (in expectation, against an oblivious adversary), then OWCycAP with cut arrivals
on `(L, c)` has one; and if the given algorithm is deterministic, so is the new one (`det = true`).

**Formalization Note.** Stated per instance: the hypothesis is about the one TL instance the
reduction of §3.1 produces. Unit costs on `L` transport to unit costs on `P_L`, so this covers the
unweighted and the weighted problem. `det = false` is the randomized statement, `det = true` the
deterministic one (§2.2 defines both ratios). -/
theorem theorem_1_10 (n : ℕ) (L : Finset (Sym2 (Fin n))) (hL : ∀ ℓ ∈ L, ¬ ℓ.IsDiag)
    (c : Sym2 (Fin n) → ℝ) (c' : ℝ × ℝ → ℝ) (hc' : ∀ ℓ ∈ L, c' (linkPoint ℓ) = c ℓ) (α : ℝ)
    (det : Bool)
    (hTL : ∃ A : RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)), (det = true → A.IsDeterministic) ∧
      IsCompetitive (tlInstance (linkPoints L) c') A α) :
    ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)), (det = true → A.IsDeterministic) ∧
      IsCompetitive (cycleInstance n L c) A α := by sorry

end OnlineCAP
