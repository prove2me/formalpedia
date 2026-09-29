-- Prove2me | Theorems.Thm_MarkovEntanglement_resolvent_identity
-- name    : MarkovEntanglement.resolvent_identity
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T05:23:55.660295+00:00
-- url     : https://prove2.me/theorems/be9cac85-536c-4d79-9616-fcaa4b993a35
-- title:
--   Resolvent identity for matrix inverses
-- statement:
--   ## Statement
--
--   **Theorem (resolvent identity).** Let $P, P' \in \mathbb{R}^{n \times n}$ be square
--   matrices such that $I - P$ and $I - P'$ are both invertible. Then
--
--   $$(I - P')^{-1} - (I - P)^{-1} \;=\; (I - P')^{-1}\,(P' - P)\,(I - P)^{-1}.$$
--
--   ## Notes
--
--   This is the **resolvent identity** (also called the second resolvent identity, or the
--   push-through identity for inverses), specialised to the operators $I - P$ and $I - P'$.
--   It converts a difference of *inverses* — an object that is hard to bound directly —
--   into the *perturbation* $P' - P$ sandwiched between two inverses, which is what makes
--   perturbation bounds on Markov chains tractable.
--
--   For a discounted Markov chain, $(I - \gamma P)^{-1}$ is the resolvent whose entries are
--   the discounted occupancy measures, so this identity is the standard first step in
--   comparing the value functions of two chains whose transition matrices are close: bound
--   $\|P' - P\|$, then propagate that bound through the two resolvents.
--
--   One caveat worth stating, because the naming invites the mistake: the hypotheses **exclude
--   transition matrices themselves**. If $P$ is row-stochastic then every row of $I - P$ sums to
--   zero, so $(I-P)\mathbf{1} = 0$ and $\det(I-P) = 0$ is not a unit. The identity is applied to
--   the *discounted* matrix $\gamma P$ with $\gamma < 1$, for which $I - \gamma P$ is invertible;
--   it says nothing about $I - P$ for a transition matrix $P$.
--
--   Mathlib carries `Commute.inv_sub_inv` for commuting elements of a group with zero, but
--   matrices do not commute in general and the identity above holds without any commutation
--   hypothesis, so it is stated here in the form actually needed. The statement is generic
--   in the index type and does not mention Markov chains, so it is reusable for any
--   perturbation argument about matrix inverses.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 1, p. 17; quoted there from Farias, Gupta and Ruan (2023), Lemma 1

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem resolvent_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P P' : Matrix ι ι ℝ) (hP : IsUnit (1 - P).det) (hP' : IsUnit (1 - P').det) :
    (1 - P')⁻¹ - (1 - P)⁻¹ = (1 - P')⁻¹ * (P' - P) * (1 - P)⁻¹ := by
  sorry

end MarkovEntanglement
