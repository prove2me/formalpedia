-- Prove2me | Theorems.Thm_JMMS_exists_subshift_conjugate_iff_exists_isSeparatingPartition
-- name    : JMMS.exists_subshift_conjugate_iff_exists_isSeparatingPartition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:47.513963+00:00
-- url     : https://prove2.me/theorems/e9aab5c9-d848-4940-9d3f-78723ab220ef
-- title:
--   JMMS, Lemma 5.10 — a Cantor system is a subshift iff a finite clopen partition separates points
-- statement:
--   Let a group $\Gamma$ act by homeomorphisms on a Cantor space $X$. Then $X$ is equivariantly homeomorphic to a $\Gamma$-subshift over a finite alphabet if and only if there is a finite partition $P$ of $X$ into clopen sets such that for all $x \ne y$ some translate $\gamma P$ separates $x$ and $y$.
--
--   JMMS, pp. 20–21: “Recall the following elementary criterion to establish whether a Cantor $\Gamma$-system is conjugate to a subshift. For a proof see e.g. [dC13, Fait 2.2]. Lemma 5.10. Let $(\Gamma, X)$ be a Cantor $\Gamma$-system. then $(\Gamma, X)$ is conjugate to a $\Gamma$-subshift over a finite alphabet if and only if there exists a finite partition $P$ of $X$ into clopen sets so that the partition $\bigvee_{\gamma\in\Gamma} \gamma P$ is the point partition of $X$ (i.e. for any $x \ne y \in X$ there exists $\gamma \in \Gamma$ so that the partition $\gamma P$ separates $x$ and $y$).”
--
--   *Formalization note.* A finite alphabet is $\{0, \dots, k-1\}$ for some $k$. Conjugacy is a homeomorphism commuting with the actions. The action is assumed to be by homeomorphisms (each translation is continuous).
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), pp. 20–21, Lemma 5.10

import Mathlib
import Definitions.Def_CantorSystems

open CantorSystems

namespace JMMS

theorem exists_subshift_conjugate_iff_exists_isSeparatingPartition
    {Γ X : Type*} [AddGroup Γ] [TopologicalSpace X] [AddAction Γ X] [ContinuousConstVAdd Γ X]
    (hX : IsCantorSpace X) :
    (∃ k : ℕ, ∃ S : Subshift Γ (Fin k), ∃ e : X ≃ₜ S,
      ∀ (γ : Γ) (x : X), e (γ +ᵥ x) = γ +ᵥ e x) ↔
    ∃ k : ℕ, ∃ p : X → Fin k, IsClopenPartition p ∧ IsSeparatingPartition Γ p := by
  sorry

end JMMS
