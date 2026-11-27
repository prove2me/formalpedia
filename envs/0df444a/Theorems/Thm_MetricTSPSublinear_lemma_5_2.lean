-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_5_2
-- name    : MetricTSPSublinear.lemma_5_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:05:28.215813+00:00
-- url     : https://prove2.me/theorems/cd1f3dd2-75f0-4da5-891b-048cee03a01d
-- title:
--   Lemma 5.2 (cost of the net expansion)
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$ with minimum spanning tree $T$, write $M=w(T)$, $K$ for the cut LP value of $V$ and $D=M-K$, and for $S\subseteq V$ let $T\langle S\rangle$ be the minimal subtree of $T$ spanning $S$ and $K(S)$ the cut LP value of the metric induced on $S$.
--
--   Let $T_0$ be a dominated shortening of $T$ (same edges, weights $0\le w_{T_0}(e)\le w_T(e)$, and $d_{T_0}(u,v)\le d(u,v)$ for all $u,v$), and let $S,N\subseteq V$ satisfy the stopping condition
--   $$K(S\cup N)-K(S)\le \theta .$$
--   Let $T_1$ be obtained from $T_0$ by setting to zero the weight of every edge of the net expansion $E_N=T\langle S\cup N\rangle\setminus T\langle S\rangle$. Then
--
--   1. $T_1$ is again a dominated shortening of $T$;
--   2. $w(T_0)-w(T_1)\le 2D+\theta$;
--   3. if $w(T_0)\ge K-D$, then $w(T_1)\ge K-3D-\theta$.
--
--   In the paper $\theta=\varepsilon\widehat M$, and $T_0$ is the shortening of Lemma 4.3. The lemma bounds the cost of discarding the part of the comparison tree between the core terminals $S$ and the final $r$-net $N$, after which the remaining positive part of $T_1$ splits into the core $T_1\langle S\rangle$ and subtrees of height at most $r$ hanging from $T_1\langle S\cup N\rangle$.
--
--   **Formalization Note** The algorithmic content of Lemma 5.2 (query count and the sizes of $S$ and $N$) is not part of this statement; only the bound on the shortening, which is what the later analysis uses.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §5.2, p.16 (PDF p.18), Lemma 5.2 and its proof (p.17), using Lemma 4.4.

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_hull
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMSTOf

open scoped Classical

namespace MetricTSPSublinear

/-- **Lemma 5.2 (structural part).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §5.2, p.16 (PDF p.18): "The new tree T1, obtained by shortening E_N = T0⟨S ∪ N⟩ \ T0⟨S⟩, satisfies
w(T0) − w(T1) ≤ 2D + εM̂, and therefore, w(T1) ≥ K − 3D − εM̂." The stopping condition (6) is
`K(S ∪ N) − K(S) ≤ εM̂`, written here as `≤ θ`.

For a metric `d`, an MST `E`, a dominated shortening `w0` of `E` and point sets `S, N` with
`K(S ∪ N) − K(S) ≤ θ`, setting `w0` to zero on the edges of `T⟨S ∪ N⟩` outside `T⟨S⟩` gives a dominated shortening
`w1` with `w(T0) − w(T1) ≤ 2D + θ`, and `w(T1) ≥ K − 3D − θ` whenever `w(T0) ≥ K − D`.

**Formalization Note.** `T0` and `T` have the same edges, so `T0⟨S∪N⟩ \ T0⟨S⟩` is the edge set
`hull E (S ∪ N) \ hull E S`. The algorithmic parts of the lemma (query count, sizes of `S` and `N`) are not part of
this statement. -/
theorem lemma_5_2 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) (w0 : Sym2 (Fin n) → ℝ) (hw0 : IsDominatedShortening d E w0)
    (S N : Finset (Fin n)) (θ : ℝ) (hstop : cutLP d (S ∪ N) - cutLP d S ≤ θ) :
    IsDominatedShortening d E (fun e => if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e) ∧
      ∑ e ∈ E, w0 e - ∑ e ∈ E, (if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e) ≤
        2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + θ ∧
      (cutLP d Finset.univ - (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ ∑ e ∈ E, w0 e →
        cutLP d Finset.univ - 3 * (DoublingMST.mstWeight d - cutLP d Finset.univ) - θ ≤
          ∑ e ∈ E, (if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e)) := by sorry

end MetricTSPSublinear
