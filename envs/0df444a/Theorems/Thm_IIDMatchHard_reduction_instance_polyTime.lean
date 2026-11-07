-- Prove2me | Theorems.Thm_IIDMatchHard_reduction_instance_polyTime
-- name    : IIDMatchHard.reduction_instance_polyTime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:48.106418+00:00
-- url     : https://prove2.me/theorems/7e8415bd-37b2-4b81-a1fc-895173de2ccd
-- title:
--   Proof of Theorem 3.1, p.23 — the instance map $G\mapsto I(\tilde G,c/B)$ is polynomial-time
-- statement:
--   Fix a rational $c>0$ and an integer $B\ge1$, and put $\lambda=c/B$. For a graph $G$ on $N$ vertices, let $I(\tilde G,\lambda)$ be the rational input built on the blow-up $\tilde G$ of $G$. Then
--
--   1. some polynomial-time machine maps the binary encoding of $G$ to the binary encoding of $I(\tilde G,\lambda)$;
--   2. the online optimum of this input is $\mathrm{OPT}(I(\tilde G,\lambda))$ of the instance of §3.1 on $\tilde G$;
--   3. if $N\ge1$, the input is an instance of Theorem 3.1, with every type having two distinct neighbors and positive probabilities summing to one, and it has $2NB$ offline vertices;
--   4. if $G$ is cubic, the total rate is $R=(1+3c)NB$.
--
--   This is the instance map of the reduction from approximating $C(G)$ to approximating the online optimum.
--
--   Differences from the source:
--   - reading: "the algorithm runs in polynomial time" (for the construction of I(G̃, λ)) → a Cook machine computes encInst (redInst c B H) from encGraph H in polynomial time; reason: the input and output are the binary encodings
--   - reading: "I(G̃, λ) is an instance of Theorem 3.1" (for the graphs the reduction queries, m ≥ N₀) → Inst.Valid when the graph has at least one vertex; reason: for N = 0 the instance has no types and cannot have probabilities summing to one; the reduction never queries it
--   - encoding: I(G̃, λ) with its vertices and types → an explicit enumeration (redInst) and the identity of its online optimum with that of cutInst (blowUp G B) (c/B); reason: a relabelling; same instance
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), proof of Theorem 3.1, App. B.9, p.23 (PDF p.24)

import Definitions.Def_IIDMatchHard_Reduction
import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

open NSWApxHard.Reduction

namespace IIDMatchHard

/-- **The instance map of the reduction** (proof of Theorem 3.1). For a rational `c > 0` and an
integer `B ≥ 1`, let `λ = c/B`. The map `H ↦ I(G̃, λ)` (as the rational input `redInst c B H`)
is computable in polynomial time on the binary encodings, it describes `I(G̃, λ)` faithfully,
it is an instance of Theorem 3.1 when `G` has a vertex, and for cubic `G` the total rate is
`R = (1 + 3c)nB`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), proof of Theorem 3.1, p.23 (PDF p.24): "Otherwise, we let λ = c/B, so
that R = (1 + 3c)nB. Then I(G̃, λ) is an instance of Theorem 3.1 with 2nB offline vertices. …
As c and B are constants, the algorithm runs in polynomial time."

**Formalization Note.** `c` and `B` are fixed before the machine. The input graph is encoded by
`encGraph` (`N`, then the adjacency matrix), the instance by `encInst`. -/
theorem reduction_instance_polyTime (c : ℚ) (hc : 0 < c) (B : ℕ) (hB : 1 ≤ B) :
    (∃ h : List Bool → List Bool, CookPvsNP.PolyTimeComputable h ∧
        ∀ H : GraphInput, h (encGraph H) = encInst (redInst c B H)) ∧
      (∀ H : GraphInput, onlineOpt (redInst c B H) = OPT (cutInst (blowUp H.G B) ((c : ℝ) / B))) ∧
      (∀ H : GraphInput, 1 ≤ H.N → (redInst c B H).Valid ∧ (redInst c B H).nOff = 2 * (H.N * B)) ∧
      (∀ H : GraphInput, IsCubic H.G →
        totalRate (blowUp H.G B) ((c : ℝ) / B) = (1 + 3 * (c : ℝ)) * H.N * B) := by sorry

end IIDMatchHard
