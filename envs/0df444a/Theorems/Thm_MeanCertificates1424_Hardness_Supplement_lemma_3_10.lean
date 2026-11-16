-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_3_10
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:58:28.125297+00:00
-- url     : https://prove2.me/theorems/d65c6e84-bd26-40f8-a23c-acf410100e99
-- title:
--   Lemma 3.10 — the incidence endpoint gadget
-- statement:
--   Let $H$ be a graph with $r$ vertices, $m_H$ edges and no isolated vertices, $1\le p\le m_H$, and $\nu_p(H)=\min\{|V(F)|:F\subseteq E(H),|F|=p\}$. Its **incidence split graph** $G_H$ has the $r$ original vertices as an independent set, one vertex per edge, the edge vertices forming a clique, each adjacent to its two endpoints; it has $N=r+m_H$ vertices. Set $h=p$ (so $b=N-p$), $L=1$, $\epsilon=0$, no audits, uniform weights. Clique vertices report $0$ and every independent vertex $v$ reports $y_v$ with $|y_v|>2$. Assume
--
--   (a) $p>r$, or (b) $p\ge 2$ and $|y_v-y_{v'}|>3$ for all distinct independent $v,v'$.
--
--   Then the feasible class is nonempty, symmetric and contained in $[-2,2]^N$, and
--   $$u(y)=-\ell(y)=\frac{m_H-p+2r-\nu_p(H)}{N}.$$
--
--   The gadget is the common step of the reductions of Theorems 3.11 and 3.12.
--
--   Differences from the source: none.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 3.10, printed p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 3.10, printed p.11 / PDF p.13. `H` has `r` vertices, `m_H` edges and no isolated
vertices, `1 ≤ p ≤ m_H`; on the incidence split graph `G_H` (`N = r + m_H` vertices) take
`h = p` (`b = N − p`), `L = 1`, `ε = 0`, no audits, uniform weights, clique (edge) vertices
reporting `0` and independent (original) vertices reporting `|y_v| > 2`. Under (a) `p > r`, or
(b) `p ≥ 2` and `|y_v − y_{v'}| > 3` for distinct independent `v, v'`: the feasible class is
nonempty, symmetric, contained in `[−2, 2]^N`, and `u(y) = −ℓ(y) = (m_H − p + 2r − ν_p(H))/N`. -/
theorem lemma_3_10 {r : ℕ} (H : SimpleGraph (Fin r)) (p : ℕ)
    (y : Fin (r + edgeCount H) → ℝ)
    (hiso : ∀ i : Fin r, ∃ j, H.Adj i j) (hp1 : 1 ≤ p) (hpm : p ≤ edgeCount H)
    (hcl : ∀ v : Fin (r + edgeCount H), r ≤ v.val → y v = 0)
    (hind : ∀ v : Fin (r + edgeCount H), v.val < r → 2 < |y v|)
    (hcase : r < p ∨ (2 ≤ p ∧ ∀ v v' : Fin (r + edgeCount H), v.val < r → v'.val < r →
      v ≠ v' → 3 < |y v - y v'|)) :
    let I : Inst :=
      { n := r + edgeCount H, graph := incidenceGraph H, budget := r + edgeCount H - p,
        lip := 1, noise := 0, reports := y, weights := uniformW (r + edgeCount H),
        audits := ∅, lo := 0, hi := 0 }
    (CI I).Nonempty ∧ (∀ x ∈ CI I, -x ∈ CI I) ∧ (∀ x ∈ CI I, ∀ v, |x v| ≤ 2) ∧
    upper I = (((((edgeCount H : ℝ) - p + 2 * r - nuP H p) / (r + edgeCount H)) : ℝ) : EReal) ∧
    lower I = (((-(((edgeCount H : ℝ) - p + 2 * r - nuP H p) / (r + edgeCount H))) : ℝ) :
      EReal) := by sorry

end MeanCertificates1424.Hardness.Supplement
