-- Prove2me | Theorems.Thm_JMMS_entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
-- name    : JMMS.entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:39.518693+00:00
-- url     : https://prove2.me/theorems/16431ef2-cb33-4a9a-8222-9bde768a1a00
-- title:
--   JMMS, §5.3 — Matte Bon's Theorem 1.2 for subshifts of a virtually cyclic abelian group
-- statement:
--   Let $\Gamma$ be an abelian group containing an element of infinite order whose multiples have finite index. Let $X \subseteq A^\Gamma$ be a $\Gamma$-subshift over a finite alphabet whose points with trivial stabiliser are dense. Suppose that, for some finite generating set $T$ of $\Gamma$ and some finite clopen partition $P$ whose translates separate points, the complexity satisfies $\rho_{T,P}(n) \le C n^\alpha$ for all $n \ge 1$, with $\alpha < 2$. Then for every finitely supported symmetric probability measure $\mu$ on the topological full group $[[\Gamma]]$, there is $C'$ with $H(\mu^{*n}) \le C' n^{\alpha/2}(\log n)^{1+\alpha/2}$ for all $n \ge 2$, and the random-walk entropy of $\mu$ is $0$.
--
--   JMMS, p. 22, in the proof of Part 1 of Theorem 5.4: “(The statement of [MB14, Theorem 1.2] assumes that $\Lambda = \mathbf Z$, but the proof extends with no changes if $\Lambda$ is virtually cyclic.)”
--
--   *Formalization note.* This is the extension that JMMS asserts in parentheses; Part 1 of Theorem 5.4 itself is the mission's Theorem 1.10(i). It is stated with JMMS's complexity $\rho_{T,P}$ (p. 21) in place of word complexity. JMMS applies it to subgroups $\Lambda$ of $\mathbf R/\mathbf Z$, so $\Gamma$ is abelian. “Non-periodic” is read as “trivial stabiliser”, which holds in JMMS's application, where $\Lambda$ acts freely; for $\Gamma = \mathbf Z$ it is Matte Bon's notion. The bound is assumed for one generating set and one separating clopen partition. The thresholds $n \ge 1$ and $n \ge 2$ are as in Matte Bon's theorem.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 22, proof of Theorem 5.4, Part 1 (the extension of Matte Bon, Theorem 1.2, to virtually cyclic Λ)

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_ErschlerZheng_Walks

open CantorSystems ErschlerZheng

namespace JMMS

theorem entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
    {Γ A ι : Type*} [AddCommGroup Γ]
    (hΓ : ∃ γ : Γ, addOrderOf γ = 0 ∧ (AddSubgroup.zmultiples γ).FiniteIndex)
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift Γ A)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0})
    (T : Finset Γ) (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    [Finite ι] (p : S → ι) (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p)
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup Γ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 := by
  sorry

end JMMS
