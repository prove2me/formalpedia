-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_4
-- name    : LipStableCA.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:31.077371+00:00
-- url     : https://prove2.me/theorems/c52fc2b7-9dba-4497-84f5-e8b2149b58d0
-- title:
--   Lemma 5.4 — menu rigidity
-- statement:
--   Let $(S,p)$ be a universally truthful mechanism with $\mathrm{Lip}(S)<\infty$, and fix a bidder $i$ and reports $v_{-i}$ of the other bidders. For a seed $\omega$, let $R^+_\omega$ be the set of nonempty attained bundles of bidder $i$ in the deterministic mechanism at $\omega$, with prices $\pi_\omega$, and let $B_\omega=\bigcup_{Q\in R^+_\omega}Q$. With probability one, whenever $B_\omega\ne\emptyset$, the bundle $B_\omega$ is attained and
--   $$\pi_\omega(B_\omega)\le\pi_\omega(Q)\qquad\text{for every }Q\in R^+_\omega.$$
--   Consequently, with probability one, bidder $i$ receives either $B_\omega$ or $\emptyset$ at every strictly monotone report.
--
--   In words, a universally truthful mechanism with a finite Lipschitz constant makes each bidder a take-it-or-leave-it offer of a single bundle chosen without looking at her report. This is the key lemma behind the impossibility theorem.
--
--   **Formalization Note.** The event of the lemma quantifies over uncountably many reports and need not be measurable. The statement is an almost-everywhere one, that is, its failure set has outer measure zero. Prices are stated through payments at reports, by Lemma 5.3(i).
--
--   Differences from the source:
--   - reading: "with probability one" of an event that need not be measurable, written $\Pr[E]=0$ in the proof → `∀ᵐ`: the failure set has outer measure $0$; reason: the proof's steps go through unchanged with outer measure (paper.md decision 5)
--   - encoding: prices $\pi_\omega$ of attained bundles → payments at reports attaining the bundle; reason: at a truthful seed the two agree by Lemma 5.3(i)
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.4, p.22

import Definitions.Def_LipStableCA_Mechanism
import Definitions.Def_LipStableCA_IsLipschitz
import Definitions.Def_LipStableCA_offerBundle
open MeasureTheory

namespace LipStableCA

/-- **Lemma 5.4.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.22. **Formalization Note.** `∀ᵐ`: the failure set has outer measure `0`: the proof's steps go through unchanged with outer measure (paper.md decision 5). payments at reports attaining the bundle: at a truthful seed the two agree by Lemma 5.3(i). measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). -/
theorem lemma_5_4 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Mechanism n m Ω) (hM : M.Measurable) (hUT : M.IsUT μ) (hLip : ∃ K, IsLipschitz (M.law μ) K)
    (i : Fin n) (v : Profile n m) (hv : IsProfile v) :
    ∀ᵐ ω ∂μ,
      (offerBundle (fun u => M.alloc u ω) i v ≠ ∅ →
        ∃ u₀, IsValuation u₀ ∧
          (M.alloc (Function.update v i u₀) ω).1 i = offerBundle (fun u => M.alloc u ω) i v ∧
          ∀ u, IsValuation u → (M.alloc (Function.update v i u) ω).1 i ≠ ∅ →
            M.pay (Function.update v i u₀) ω i ≤ M.pay (Function.update v i u) ω i) ∧
      (∀ u, IsValuation u → IsStrictlyMonotone u →
        (M.alloc (Function.update v i u) ω).1 i = offerBundle (fun u => M.alloc u ω) i v ∨
          (M.alloc (Function.update v i u) ω).1 i = ∅) := by sorry

end LipStableCA
