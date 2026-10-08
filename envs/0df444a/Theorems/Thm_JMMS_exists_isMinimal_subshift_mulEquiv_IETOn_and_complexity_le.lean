-- Prove2me | Theorems.Thm_JMMS_exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
-- name    : JMMS.exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:57.839984+00:00
-- url     : https://prove2.me/theorems/424bc7da-cd84-4dc7-82d2-7838d98b4fbc
-- title:
--   JMMS, Proposition 5.11 and Lemma 5.13 — the subshift realizing IET(Λ; Σ) has complexity O(n^d) for d = rk_Q(Λ)
-- statement:
--   Let $\Lambda \le \mathbf R/\mathbf Z$ be infinite and finitely generated, and let $\Sigma \subset \mathbf R/\mathbf Z$ be finite and nonempty. Then there are $X$, $\pi$ and $h$ as in Proposition 5.11 such that, moreover, if $\mathrm{rk}_{\mathbf Q}(\Lambda) = d$, then for every finite generating set $T$ of $\Lambda$ and every finite clopen partition $P$ of $X$ whose translates separate points there is $C > 0$ with $\rho_{T,P}(n) \le C n^d$ for all $n \ge 1$.
--
--   JMMS, p. 22: “Lemma 5.13. Let $(\Lambda, C)$ the Cantor minimal system constructed in the previous proposition, and assume that $\mathrm{rk}_{\mathbf Q}(\Lambda) = d$. Then for every generating set $S$ of $\Lambda$ and every partition $P$ satisfying Lemma 5.10 there exists a constant $C > 0$ so that $\rho_{S,P}(n) \le Cn^d$.”
--
--   *Formalization note.* Lemma 5.13 is about the system built in the proof of Proposition 5.11, so it is stated together with the conclusion of that proposition, in the corrected form described in that statement's note. The generating set is finite, as the word metric in $\rho_{S,P}$ requires. The bound is for $n \ge 1$: at $n = 0$, $\rho(0) \ge 1 > C \cdot 0^d$ when $d \ge 1$.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), pp. 21–22, Proposition 5.11 and Lemma 5.13

import Mathlib
import Definitions.Def_CantorSystems

open CantorSystems IntervalExchange

namespace JMMS

theorem exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      (∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x)) ∧
      ∀ d : ℕ, rationalRank Λ = d →
        ∀ T : Finset Λ, AddSubgroup.closure (T : Set Λ) = ⊤ →
        ∀ (m : ℕ) (p : S → Fin m), IsClopenPartition p → IsSeparatingPartition Λ p →
          ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Λ) p n : ℝ) ≤ C * (n : ℝ) ^ d := by
  sorry

end JMMS
