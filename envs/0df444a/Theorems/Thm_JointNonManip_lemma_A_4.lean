-- Prove2me | Theorems.Thm_JointNonManip_lemma_A_4
-- name    : JointNonManip.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:08.323796+00:00
-- url     : https://prove2.me/theorems/0fc69295-06a3-4b49-832b-e9593c07169f
-- title:
--   Lemma A.4 — for $|A_0|\ge2$ a horizon-aware profile stays near $S_{\mathrm{NE}}$, statically attains every point of $E_{\mathrm{NE}}$, and has no swap regret
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities in $[-1,1]$, and suppose $|A_0|\ge2$. Then there is a horizon-aware profile $\mathcal A'_{\mathcal L}$ of learner algorithms, whose mixed strategies depend only on the optimizer's past actions, such that
--
--   1. $\displaystyle\sup_{\pi_T}\mathbb E\big[\operatorname{dist}_1(\bar k_T,S_{\mathrm{NE}})\big]=o(1)$, where $\bar k_T=\frac1T\sum_{t=1}^Te_{c^{(t)}}\otimes q^{(t)}$;
--   2. $\displaystyle\sup_{s\in E_{\mathrm{NE}}}\ \inf_{z\in\Delta(A_0)}\big\|\varphi_T(z^{\otimes T},\mathcal A'_{\mathcal L})-s\big\|_1=o(1)$;
--   3. $\displaystyle\sup_{\pi_T}\mathbb E\big[R_i^{\mathrm{sw}}(T)\big]=o(T)$ for every learner $i\in\mathcal L$.
--
--   This is the menu-completion step: together with Lemma 3.1 it yields Theorem 3.3.
--
--   Differences from the source:
--   - reading: Algorithm 1 admits a horizon-aware augmentation A'_L → there exists a horizon-aware public-history profile P; reason: 'augmentation of Algorithm 1' constrains how the profile is built, not what it is; the construction on p.27 is one such profile
--   - encoding: dist₁(k̄_T, S_NE) → l1InfDist, a real infimum of ℓ₁ distances over S_NE; reason: S_NE is nonempty (Nash's theorem) and the distances are ≥ 0, so the infimum is the source's
--   - encoding: learner algorithms whose mixed strategies are determined by the optimizer's past actions; optimizer policies choosing y(t) adaptively from the history and the current q(t); φ_T and E[R^sw_i(T)] as expectations → Profile (lotteries x T t (c(1..t)) i); Policy (lotteries y(t) as functions of the past optimizer and learner actions); expectations as finite sums over trajectories weighted by trajWeight; reason: the model of p.4: q(t) is a function of the history and the fixed profile, so it is not a separate argument of the policy
--   - encoding: o(T) and o(1) uniformly over optimizer policies; sup_π ⟨u₀, φ_T(π)⟩ ≤ sup_y ⟨u₀, φ_T(y^{⊗T})⟩ + o(1); inf_y ‖·‖₁ = o(1) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ π (NoSwapRegret, JointlyNonManipulable: every π is matched within ε by a static y); ∃ y within ε; reason: the definition of o(·); a supremum (infimum) is at most (at least) a bound up to ε iff every element is (some element is) within ε
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Lemma A.4, p.26 (proof pp.27–28)

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Lemma A.4: menu completion** (Collina, Fullerton, Liu & Weinberg, *Non-manipulability and
Approachability Beyond Two-Player Games*, manuscript (STOC 2027 submission), Lemma A.4, p.26).

Suppose `|A₀| ≥ 2` (finite game, nonempty action sets, learner utilities in `[−1, 1]`). Then
there is a horizon-aware public-history profile `A'_L` of learner algorithms such that
1. `sup_{π_T} E[dist₁(k̄_T, S_NE)] = o(1)`, where `k̄_T = (1/T) ∑ₜ e_{c(t)} ⊗ q(t)`;
2. `sup_{s ∈ E_NE} inf_{z ∈ ∆(A₀)} ‖φ_T(z^{⊗T}, A'_L) − s‖₁ = o(1)`;
3. `sup_{π_T} E[R_i^sw(T)] = o(T)` for every learner `i`.

**Formalization Note** "Algorithm 1 admits a horizon-aware augmentation `A'_L`" is read as the
existence of such a profile. Each `o(·)` is `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀`, uniformly over policies
(1, 3) or over `s ∈ E_NE` (2). -/
theorem lemma_A_4 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1)
    (hA0 : 2 ≤ Fintype.card A0) :
    ∃ P : Profile A0 Act,
      (∀ ε > 0, ∃ T0 : ℕ, ∀ T ≥ T0, ∀ π : Policy A0 Act T,
        ∑ ω : Fin T → A0 × ((i : L) → Act i),
          trajWeight P π ω * l1InfDist (pathCSP P T (fun s => (ω s).1)) (SNE u) ≤ ε) ∧
      (∀ ε > 0, ∃ T0 : ℕ, ∀ T ≥ T0, ∀ s ∈ ENE u,
        ∃ (z : A0 → ℝ) (hz : AGT.IsLottery z), l1dist (expCSP P (Policy.static z hz T)) s ≤ ε) ∧
      NoSwapRegret u P := by sorry

end JointNonManip
