-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_6_4
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:06:49.815024+00:00
-- url     : https://prove2.me/theorems/afddce72-f5e6-42b5-9e08-c8948be314d5
-- title:
--   Theorem 6.4 — exact recovery radius with fixed audits
-- statement:
--   For every fixed set $Q\subseteq V$ of exact audits, with $g_{S,Q}(v)=\min\{Ld_G(v,Q),\epsilon+Ld_G(v,V\setminus S)\}$ and $d_G(v,\emptyset)=+\infty$,
--   $$R^*_Q(G,b,L,\epsilon)=\frac1n\max_{|S|\le\min\{2b,n\}}\sum_{v\in V}g_{S,Q}(v).$$
--   The radius is finite iff $Q\ne\emptyset$ or $2b<n$, and then the midpoint attains it. The maximum may be restricted to $S\subseteq V\setminus Q$.
--
--   Audits help by removing vertices from the regions that replaced reports can hide.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; with $L>0$, $L\cdot\infty=\infty$.
--
--   Differences from the source: none.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 6.4, printed p.20 (PDF p.22), proof printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 6.4, printed p.20 / PDF p.22 (proof p.21 / PDF p.23). For every fixed audit set `Q`,
`R*_Q(G, b, L, ε) = n⁻¹ max_{|S| ≤ min{2b, n}} ∑_v g_{S,Q}(v)` in `[0, ∞]`; it is finite iff
`Q ≠ ∅` or `2b < n`, and then the midpoint attains it; the maximum may be restricted to
`S ⊆ V ∖ Q`. -/
theorem theorem_6_4 {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (Q : Finset (Fin n))
    (hn : 1 ≤ n) (hG : G.Connected) (hL : 0 < L) (hε : 0 ≤ ε) (hb : b ≤ n) :
    minimaxRadius G b L ε Q (uniformW n) = (n : ENNReal)⁻¹ *
      (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ min (2 * b) n).sup
        (fun S => ∑ v, gSQ G L ε S Q v) ∧
    (minimaxRadius G b L ε Q (uniformW n) ≠ ⊤ ↔ Q.Nonempty ∨ 2 * b < n) ∧
    ((Q.Nonempty ∨ 2 * b < n) →
      worstCase G b L ε Q (uniformW n) (midEstimator G b L ε Q (uniformW n)) =
        minimaxRadius G b L ε Q (uniformW n)) ∧
    minimaxRadius G b L ε Q (uniformW n) = (n : ENNReal)⁻¹ *
      (Finset.univ.filter fun S : Finset (Fin n) => Disjoint S Q ∧ S.card ≤ min (2 * b) n).sup
        (fun S => ∑ v, gSQ G L ε S Q v) := by sorry

end MeanCertificates1424.Hardness.Supplement
