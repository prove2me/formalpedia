-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_4_1
-- name    : GaussDiffSVP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:39.115687+00:00
-- url     : https://prove2.me/theorems/93d672aa-bafa-4068-9fb4-8e541fdfe4d4
-- title:
--   Lemma 4.1 — exact factorial recursion $m_a = \Phi_q(m_L,m_R)$ and (23)
-- statement:
--   Consider a merge of two record lists that are independent given the merge's fixed information. Every ordered pair of child records $(i,j)$ is activated with probability $q(X_i,Y_j)$, distinct pair coins being pairwise independent given the completed child lists, and the full merge keeps one record $T(X_i,Y_j)$ for every activated pair. Then
--   $$m_a = \Phi_q(m_L,m_R),$$
--   $$S_a^{\mathrm{act}} = \Psi_q(S_L^{\mathrm{act}},S_R^{\mathrm{act}}) + \Psi_q(\Delta_*m_L,S_R^{\mathrm{act}}) + \Psi_q(S_L^{\mathrm{act}},\Delta_*m_R).$$
--   The three terms of the second identity are the pairs of output records that use four distinct child records, share a left record, or share a right record. It closes the first two moments under one merge without tracking the joint law of the lists.
--
--   Differences from the source:
--   - encoding: conditional moments given the merge's fixed information → moments of the laws $\mu_L,\mu_R$, for arbitrary laws; reason: the statement for every law covers every value of the information
--   - encoding: records with IDs; activation coins → list positions; a coin kernel with marginals $q$ and the pairwise product rule; reason: same objects
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 4.1, p.23 (setting §4.1, pp.22–23)

import Mathlib
import Definitions.Def_GaussDiffSVP_intensity
import Definitions.Def_GaussDiffSVP_factMoment
import Definitions.Def_GaussDiffSVP_transport1
import Definitions.Def_GaussDiffSVP_transport2
import Definitions.Def_GaussDiffSVP_diagM
import Definitions.Def_GaussDiffSVP_IsCoinKernel
import Definitions.Def_GaussDiffSVP_fullMergeLaw

open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 4.1 (Exact factorial recursion) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.23). Two child record lists are independent
(laws `μL`, `μR`), every ordered pair of child records `(i, j)` is activated with probability
`q(X_i, Y_j)` by pairwise independent coins (a coin kernel `κ` with marginals `q`), and the full
merge keeps one record `T(X_i, Y_j)` per activated pair. Then
`m_a = Φ_q(m_L, m_R)` (22) and
`S_a^{act} = Ψ_q(S_L^{act}, S_R^{act}) + Ψ_q(Δ_*m_L, S_R^{act}) + Ψ_q(S_L^{act}, Δ_*m_R)` (23).

**Formalization Note.** The moments are conditional on the merge's fixed information: the child
laws are the conditional laws, and the statement holds for each value of that information. All
identities are in `ℝ≥0∞`. -/
theorem lemma_4_1 {α β γ : Type*} (μL : PMF (List α)) (μR : PMF (List β)) (T : α → β → γ)
    (q : α → β → ℝ≥0∞)
    (κ : (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool))
    (hκ : IsCoinKernel q κ) :
    (∀ z, intensity (fullMergeLaw μL μR T κ) z =
        transport1 T q (intensity μL) (intensity μR) z) ∧
    ∀ z z', factMoment (fullMergeLaw μL μR T κ) z z' =
      transport2 T q (factMoment μL) (factMoment μR) z z' +
        transport2 T q (diagM (intensity μL)) (factMoment μR) z z' +
        transport2 T q (factMoment μL) (diagM (intensity μR)) z z' := by sorry

end GaussDiffSVP
