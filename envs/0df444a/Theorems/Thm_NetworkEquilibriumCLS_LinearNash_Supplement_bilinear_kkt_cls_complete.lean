-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_Supplement_bilinear_kkt_cls_complete
-- name    : NetworkEquilibriumCLS.LinearNash.Supplement.bilinear_kkt_cls_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:34.765279+00:00
-- url     : https://prove2.me/theorems/e92cf9b0-6d26-401a-82d2-47d5bc74ce7b
-- title:
--   Main Theorem 3 — exact bilinear box KKT is CLS-complete
-- statement:
--   A **bilinear polynomial** on $[0,1]^m$ is a rational quadratic
--   $p(z)=\tfrac12 z^\top Q z+c^\top z$ with $Q=Q^\top\in\mathbb Q^{m\times m}$, $c\in\mathbb Q^m$ and $Q_{ii}=0$ for every $i\in[m]$: no monomial contains the square of a variable, while linear terms and arbitrary cross terms are allowed. Write $F(z)=Qz+c$ for its gradient. A point $z\in[0,1]^m$ is an exact **KKT point** of $p$ if, for every $i$,
--
--   $$z_i>0\implies F_i(z)\le 0\qquad\text{and}\qquad z_i<1\implies F_i(z)\ge 0.$$
--
--   **Bilinear-KKT** takes such a $p$ (with $m\ge1$), given explicitly by its rational coefficients, and asks for an exact rational KKT point. With one polynomial bound on answer length chosen uniformly for all inputs,
--
--   $$\mathrm{Bilinear\text{-}KKT}\ \text{is CLS-complete}.$$
--
--   Both halves are asserted: membership (totality, polynomial-time verification, polynomial answer length, and a polynomial-time reduction to the fixed canonical CLS problem) and hardness (every problem in CLS reduces to Bilinear-KKT by a polynomial-time instance map together with a polynomial-time decoder that is correct for every accepted answer).
--
--   This companion theorem shows that the CLS-completeness of exact Quadratic-KKT survives the removal of all square terms. In the source it follows from Theorem 4.5 (Quadratic-KKT reduces to Bilinear-KKT) together with the CLS-completeness of Quadratic-KKT, and the conclusion (§6) records it as a corollary; it is not used in the proof of the mission's goal.
--
--   **Formalization Note** The statement reuses the mission's published search problem `bilinearSearch` (the restriction of `quadraticSearch` to zero-diagonal instances, with the same exact rational KKT answers) and the published `CLSComplete` and `bounded` definitions, unchanged.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: polynomially encoded exact search answers → one exponent k chosen before all inputs, with total answer length at most (input length + 1)^k + k; reason: existence of k states the uniform polynomial output guarantee without inventing a numerical degree; totality and verification are conclusions inside CLS membership
--   - encoding: a bilinear polynomial over [0,1]^m → a symmetric rational matrix Q with zero diagonal and rational vector c, objective ½zᵀQz+cᵀz, with m > 0; reason: every square-free rational quadratic is of this form (halve each cross coefficient into Q_ij = Q_ji); m = 0 has no variables and is excluded as in the base quadratic problem
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.2 (PDF 3), Main Theorem 3; Bilinear-KKT defined p.6 (PDF 7), §2.1; corollary noted p.16 (PDF 17), §6.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

namespace NetworkEquilibriumCLS.LinearNash.Supplement

/-- Anagnostides–Panageas–Yan, STOC 2027 submission #653, Main Theorem 3 (printed p. 2, PDF 3):
exact box KKT for rational quadratics with zero diagonal (`bilinearSearch`) is CLS-complete,
with one answer-length exponent `k` fixed before all inputs. Both CLS membership and
CLS-hardness are asserted. -/
theorem bilinear_kkt_cls_complete :
    ∃ k : ℕ, CLSComplete (bounded bilinearSearch k) := by sorry

end NetworkEquilibriumCLS.LinearNash.Supplement
