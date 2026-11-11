-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_14
-- name    : JainCRERepetition.Cubic.lemma_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:23.381109+00:00
-- url     : https://prove2.me/theorems/1d23e77a-e48f-4e6e-a85b-92c01132cc6f
-- title:
--   Lemma 2.14 — square-root rejection and question changes
-- statement:
--   For normalized states $\rho_z,\sigma_z$ and rejecting effects $0\le N_z\le1$, put $\alpha_z=\operatorname{Tr}N_z\sigma_z$, $\beta_z=\operatorname{Tr}N_z\rho_z$, and $\delta_z=P^2(\rho_z,\sigma_z)$. Then $|\sqrt{\beta_z}-\sqrt{\alpha_z}|\le\sqrt{\delta_z}$. For laws $p,q$ on these fixed labels, let $a_q=\mathbb E_q\alpha_z$, $e_q=\mathbb E_q\delta_z$, $r_q=\mathbb E_q\beta_z$, $r_p=\mathbb E_p\beta_z$. Then
--
--   $$\sqrt{r_q}\le\sqrt{a_q}+\sqrt{e_q},\qquad\sqrt{r_p}\le\sqrt{a_q}+\sqrt{e_q}+P(p,q).$$
--
--   If $D(q\|p)<\infty$, the last term is at most $\sqrt{(\ln2)D(q\|p)}$. The quantum spaces may depend on the label, but all states, spaces and effects stay fixed when the question law changes.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 15, Lemma 2.14, Eqs. (9)–(10); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_14
    {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Z → Type) [∀ z, Fintype (I z)] [∀ z, DecidableEq (I z)]
    (ρ σ N : (z : Z) → Op (I z))
    (hρ : ∀ z, IsState (ρ z)) (hσ : ∀ z, IsState (σ z))
    (hN : ∀ z, (N z).PosSemidef ∧ (1 - N z).PosSemidef)
    (p q : Law Z) :
    let α := fun z => (N z * σ z).trace.re
    let β := fun z => (N z * ρ z).trace.re
    let δ := fun z => infidelity (ρ z) (σ z)
    (∀ z, |Real.sqrt (β z) - Real.sqrt (α z)| ≤ Real.sqrt (δ z)) ∧
    Real.sqrt (mean q.p β) ≤ Real.sqrt (mean q.p α) + Real.sqrt (mean q.p δ) ∧
    Real.sqrt (mean p.p β) ≤ Real.sqrt (mean q.p α) + Real.sqrt (mean q.p δ) +
      purified (diagonal p.p) (diagonal q.p) ∧
    (FiniteD (diagonal q.p) (diagonal p.p) →
      purified (diagonal p.p) (diagonal q.p) ≤
        Real.sqrt (Real.log 2 * classicald q.p p.p)) := by sorry
end JainCRERepetition.Cubic
