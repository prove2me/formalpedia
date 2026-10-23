-- Prove2me | Theorems.Thm_OSPMech_SqrtLB_lemma_13_part_2
-- name    : OSPMech.SqrtLB.lemma_13_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:59.825725+00:00
-- url     : https://prove2.me/theorems/9084f9d8-94f0-4f31-bdd8-36c9d37505ee
-- title:
--   Lemma 13, part 2, p. 13 — for i ≤ n − √n, an agent answering H at u_i receives no job
-- statement:
--   Fix an integer $c \ge 2$ and let $n = m = c^2$, so $\sqrt n = c$. Consider scheduling $m$ identical jobs on $n$ related machines with the three-value domain $D_i = \{L, M, H\}$ for every agent, where
--   $$0 < L, \qquad M \ge m \cdot L, \qquad H \ge m\sqrt n \cdot M.$$
--   Let $(\mathcal T, \mathbf p)$ be an OSP mechanism whose outcomes on $D$ schedule all $m$ jobs, and suppose it is $k$-approximate on $D$ for some $k < \sqrt n$.
--
--   Let agent $i$ be the $i$-th agent that diverges along the execution of the all-$H$ profile, and let $u_i$ be the vertex where she first diverges. If
--   $$i \le n - \sqrt n,$$
--   then for every profile $\mathbf x \in D$ compatible with $u_i$ in which agent $i$ has type $x_i = H$, the mechanism assigns no job to machine $i$:
--   $$f_i(\mathbf x) = 0.$$
--
--   Applied to the all-$H$ profile, this leaves all $m$ jobs to at most $\sqrt n$ machines, which is how Theorem 12 is concluded.
--
--   **Formalization Note.** Agents are ranked from $0$: the paper's agent $i$ has rank $r = i - 1$, and the condition is $r + 1 \le c^2 - c$. "Takes an action compatible with her type being $H$, regardless of the actions taken by the other agents" is read as: every profile of $D$ compatible with $u_i$ with $x_i = H$. The lemma is stated for agents that really diverge on the all-$H$ path. The assumption $0 < L$ reads the paper's non-negative costs with $L < M < H$; payments are a function of the declared profile. As in the paper, the lemma is a step of the proof by contradiction of Theorem 12: by that theorem no mechanism meets its hypotheses (an OSP mechanism that is $k$-approximate with $k < \sqrt n$), so its content is the implication itself, which the paper derives from OSP CMON.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, pp. 12–13, Lemma 13, part 2 (setup p. 12)

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem lemma_13_part_2 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (k : ℝ) (hk : k < c) (happrox : IsKApprox (c ^ 2) k (fun _ => {L, Mid, H}) t)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∀ x : Fin (c ^ 2) → ℝ, InDomain (fun _ => {L, Mid, H}) x → Compatible t pos x → x i = H →
      outcome t x i = 0 := by sorry
end OSPMech.SqrtLB
