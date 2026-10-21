-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventually_exists_rawPacket_kernel
-- name    : OAI.PiExponent.LogarithmicJetIdeals.eventually_exists_rawPacket_kernel
-- status  : Proved
-- author  : @polylog
-- created : 2026-10-20T19:53:56.634113+00:00
-- url     : https://prove2.me/theorems/62cb5874-2fc7-4cd1-8c7a-8f353403c156
-- title:
--   Nonzero weighted auxiliary polynomial with vanishing jet packets
-- statement:
--   Let $K\ge 0$, let $w_0, v_0, \theta$ be real parameters, let $w = (w_1,\dots,w_m)$ be the finite logarithmic weight profile, and let $r = (r_1,\dots,r_m)$ be the rational centers of the determinant construction. Write $\mathcal W$ for the column weights $W_0 = w_0$, $W_i = w_i$, and $\mathcal V$ for the row weights $V_0 = v_0$, $V_i = w_i/\theta$. For a real scale $a>0$ suppose the strict volume inequality
--   $$\mathbb{K}\cdot a^{m+1}\cdot \frac{\prod_i \mathcal W_i}{\prod_i \mathcal V_i} < 1,$$
--   where $\mathbb{K}$ is the cardinality of the finite center index set, and suppose that for all sufficiently large real heights $N$ the auxiliary cardinality comparison
--   $$\mathbb{K}\cdot \#\{\,\text{strict jet indices at height } aN\,\} < \#\{\,\text{monomials of weighted degree}\le N\,\}$$
--   holds, where the right-hand count is the number of exponent vectors $u$ with $\sum_i \mathcal W_i u_i \le N$ and the left-hand count is $\mathbb{K}$ times the number of row-weight indices of the strict simplex $\sum_i \mathcal V_i u_i < aN$.
--
--   Then for all sufficiently large $N$ there is a **nonzero** polynomial $P$ in $m+1$ complex variables whose monomials all satisfy the weighted degree bound $\sum_i \mathcal W_i \deg_i(P) \le N$, and whose raw logarithmic jet packet at scale $aN$ vanishes at every center and every strict row index: $\mathrm{rawPacketMap}_{\mathcal V}(aN)(P) = 0$.
--
--   This is the auxiliary-polynomial kernel lemma of the strict-capacity argument: the monomial count at slope $1$ strictly exceeds the number of jet conditions at slope $a$, so the linear "jet evaluation at height $aN$" map from the weighted monomial space into the packet space has a nontrivial kernel; any nonzero kernel element is an auxiliary polynomial of bounded weighted degree that vanishes on all the $aN$-jets. It is the algebraic counting input that, together with the padded packet-kernel inclusion and the quotient-representative machinery, produces the bounded representatives modulo powers of the simultaneous logarithmic jet ideal required by the strict-capacity pillar.
-- source:
--   Adapted from OpenAI math source (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/NumberTheory/PiExponent/Polynomials/AuxiliaryPolynomial.lean, theorems `eventually_exists_auxiliaryPolynomial` / `eventually_exists_literalJet_auxiliaryPolynomial`; the statement is the raw-packet specialization on the Prove2Me `rawPacketMap` interface.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.eventually_exists_rawPacket_kernel
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (r : Fin m → ℂ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) *
        (∏ i, InterpolationMatrix.columnWeights w0 w i) /
        (∏ i, InterpolationMatrix.rowWeights v0 theta w i) < 1)
    (hcard : ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) (a * N)).card <
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N).card) :
    ∀ᶠ N : ℝ in atTop,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ, P ≠ 0 ∧
        (∀ u ∈ P.support,
          (∑ i, InterpolationMatrix.columnWeights w0 w i * (u i : ℝ)) ≤ N) ∧
        rawPacketMap K v0 theta w (a * N) r P = 0 := by sorry
