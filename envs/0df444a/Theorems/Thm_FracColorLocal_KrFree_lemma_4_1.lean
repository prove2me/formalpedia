-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_4_1
-- name    : FracColorLocal.KrFree.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:42.137684+00:00
-- url     : https://prove2.me/theorems/8225a333-249c-4872-b51c-53808c6d70cf
-- title:
--   Lemma 4.1 — U_{G,u}(q) ≥ Φ_{G,u}(s) for q(v) = √(−u(v)f′(d_{G,s}(v)))
-- statement:
--   Let $G$ be a finite graph with no isolated vertices, $u>0$ an objective weight and $s$ a positive vertex weight. Set $q(v)=\sqrt{-u(v)f'(d_{G,s}(v))}$ at every vertex, where $d_{G,s}(v)=s(N(v))/s(v)$. Then
--
--   $$U_{G,u}(q)\ \ge\ \Phi_{G,u}(s).$$
--
--   This is the reverse comparison to (4.2) after a change of weights; with (4.2) it gives $\sup_{w>0}U=\sup_{s>0}\Phi$ (Corollary 4.2).
--
--   Differences from the source: none.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 17 (PDF 18), Lemma 4.1 (standing assumption u > 0 of §4, p. 16)

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Shearer
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- Lemma 4.1: with `q(v) := √(-u(v) f'(d_{G,s}(v)))`, `U_{G,u}(q) ≥ Φ_{G,u}(s)`. -/
theorem lemma_4_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (u s : V → ℝ)
    (hu : ∀ v, 0 < u v) (hiso : ∀ v, ∃ y, G.Adj v y) (hs : ∀ v, 0 < s v) :
    phiPot G u s ≤
      potential G u (fun v => Real.sqrt (-u v * deriv shearerF (weightedDegree G s v))) := by sorry

end FracColorLocal.KrFree
