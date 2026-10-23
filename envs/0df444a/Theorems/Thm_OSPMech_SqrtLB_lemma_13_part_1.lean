-- Prove2me | Theorems.Thm_OSPMech_SqrtLB_lemma_13_part_1
-- name    : OSPMech.SqrtLB.lemma_13_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:58.123336+00:00
-- url     : https://prove2.me/theorems/eda92103-16b9-49e7-925e-4b77f5623104
-- title:
--   Lemma 13, part 1, p. 13 — for i ≤ n − √n + 1, an agent diverging at u_i diverges on M and H
-- statement:
--   Fix an integer $c \ge 2$ and let $n = m = c^2$, so $\sqrt n = c$. Consider scheduling $m$ identical jobs on $n$ related machines with the three-value domain $D_i = \{L, M, H\}$ for every agent, where
--   $$0 < L, \qquad M \ge m \cdot L, \qquad H \ge m\sqrt n \cdot M.$$
--   Let $(\mathcal T, \mathbf p)$ be an OSP mechanism whose outcomes on $D$ schedule all $m$ jobs, and suppose it is $k$-approximate on $D$ for some $k < \sqrt n$.
--
--   Let agent $i$ be the $i$-th agent that diverges along the execution of the all-$H$ profile, and let $u_i$ be the vertex where she first diverges. If
--   $$i \le n - \sqrt n + 1,$$
--   then $i$ diverges on $M$ and $H$ at $u_i$: the types $M$ and $H$ of agent $i$ lead to different children of $u_i$.
--
--   This is the first step of the proof of Theorem 12: it rules out that the early diverging agents separate only $L$ from $\{M, H\}$.
--
--   **Formalization Note.** Agents are ranked from $0$: the paper's agent $i$ has rank $r = i - 1$, and the condition is $r + 1 \le c^2 - c + 1$. The lemma is stated for agents that really diverge on the all-$H$ path (the paper's "dummy nodes" for agents that never diverge are not used). The assumption $0 < L$ reads the paper's non-negative costs with $L < M < H$; payments are a function of the declared profile. As in the paper, the lemma is a step of the proof by contradiction of Theorem 12: by that theorem no mechanism meets its hypotheses (an OSP mechanism that is $k$-approximate with $k < \sqrt n$), so its content is the implication itself, which the paper derives from OSP CMON.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, pp. 12–13, Lemma 13, part 1 (setup p. 12)

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem lemma_13_part_1 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (k : ℝ) (hk : k < c) (happrox : IsKApprox (c ^ 2) k (fun _ => {L, Mid, H}) t)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c + 1)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∃ act ch, subtreeAt t pos = some (.node i act ch) ∧ act Mid ≠ act H := by sorry
end OSPMech.SqrtLB
