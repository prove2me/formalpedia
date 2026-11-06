-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_canonical_path_bound
-- name    : KawasakiSOS.Threshold.canonical_path_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:28.099651+00:00
-- url     : https://prove2.me/theorems/32cd4a1a-7e90-4819-bcdb-7396d1862627
-- title:
--   Theorem 2.3: the canonical-path bound
-- statement:
--   Let $P$ be an irreducible stochastic matrix on a finite set $V$ with at least two elements, reversible with respect to a distribution $\pi$, and let $(\gamma_{xy})$ be a system of paths of transitions, with congestion $\rho$ and maximal length $\ell$. Then the spectral gap, one minus the second-largest eigenvalue of $P$, satisfies
--
--   $$\mathrm{gap}(P)\ge\frac1{\rho\,\ell},$$
--
--   and the lazy chain $\tfrac12(I+P)$ satisfies, for every $\varepsilon\in(0,1)$,
--
--   $$\tau(\varepsilon)\le2\rho\ell\Bigl(\log\frac1{\pi_{\min}}+\log\frac1\varepsilon\Bigr).$$
--
--   This is the bound through which all upper estimates on the mixing time pass. The quantities $\rho$ and $\ell$ on the right are those of $P$, not of the lazy chain.
--
--   Differences from the source:
--   - generalization: the theorem is stated for the Kawasaki chain P → any irreducible reversible stochastic matrix on a finite set with at least two states; reason: the cited theorem is general; Lemma kawasaki_chain_facts gives the hypotheses for the Kawasaki chain
--   - generalization: paths, which "we may assume" simple → arbitrary walks of transitions; reason: simple paths are walks, so the source case is included
--   - encoding: a path for each ordered pair in Ω² → paths for pairs x ≠ y only; reason: a simple path from x to x has no edges and contributes nothing to ρ or ℓ
--   - reading: τ(ε) with ε unrestricted → ε in (0,1); reason: the range of Theorem 1.2, where the bound is used
--   - encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty; reason: Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 2.3, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_mm_mixing
import Definitions.Def_mm_basic
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_DiaconisStroock_Poincare_GraphPaths
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.CanonPaths

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 2.3, p. 6 (PDF p. 7).

Formalization Notes:
- generalization: the theorem is stated for the Kawasaki chain P → any irreducible reversible stochastic matrix on a finite set with at least two states. The cited theorem is general; Lemma kawasaki_chain_facts gives the hypotheses for the Kawasaki chain.
- generalization: paths, which "we may assume" simple → arbitrary walks of transitions. Simple paths are walks, so the source case is included.
- encoding: a path for each ordered pair in Ω² → paths for pairs x ≠ y only. A simple path from x to x has no edges and contributes nothing to ρ or ℓ.
- reading: τ(ε) with ε unrestricted → ε in (0,1). The range of Theorem 1.2, where the bound is used.
- encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty. Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free. -/
theorem canonical_path_bound {V : Type*} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (π : V → ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (hπ : IsDist π) (hrev : DetailedBalance P π) (γ : V → V → List V) (hγ : IsWalkSystem P π γ) :
    1 / (eta P π γ * (maxPathEdges γ : ℝ)) ≤ spectralGap P ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        {t : ℕ | distStationary (lazy P) π t ≤ ε}.Nonempty ∧
          (mixingTime (lazy P) π ε : ℝ) ≤
            2 * eta P π γ * (maxPathEdges γ : ℝ) * (Real.log (1 / ⨅ x, π x) + Real.log (1 / ε)) := by sorry

end KawasakiSOS.Threshold
