-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_weakMean_trace
-- name    : OAI.EntropyPhotonNumber.WeightedColumns.weakMean_trace
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-16T01:44:00.515208+00:00
-- url     : https://prove2.me/theorems/255e0d58-970b-4a9a-b43a-eab5d56aa445
-- title:
--   Trace formula for the weak annihilation mean of a weighted column decomposition
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$ be the $n$-mode bosonic Fock space with number basis $|k\rangle$, $k\in\mathbb N^n$, and write $|k|=k_1+\dots+k_n$ for the total photon number. Let $\mathcal N$ denote multiplication by $1+|k|$ (so every $\mathcal N^{-m}$, $m\ge 0$, is a bounded operator), and let $a_j$ be the annihilation operator of mode $j$, $(a_jx)(k)=\sqrt{k_j+1}\,x(k+\mathbf 1_j)$, where $\mathbf 1_j$ is the $j$-th unit index; the operators $a_j\mathcal N^{-3}$ and $a_j^\dagger\mathcal N^{-3}$ are bounded. Inner products are conjugate-linear in the first slot. A *state* is a positive bounded operator $\rho$ on $\mathcal F_n$ whose number-basis diagonal sums to $1$.
--
--   A *weighted column decomposition* $X$ of a state $\rho$ is a family $(x_i)_{i\in I}$ of vectors of $\mathcal F_n$ with $\sum_i\|x_i\|^2<\infty$, $\sum_i\|\mathcal N^{-3}x_i\|^2=1$ and $\rho=\sum_i|\mathcal N^{-3}x_i\rangle\langle\mathcal N^{-3}x_i|$. For such $X$, a real number $r$, a mode $j$ and a bounded operator $Z$ put
--   $$
--   \Lambda_{r,j}(X;Z)=(r+1)\sum_i\big\langle a_j\mathcal N^{-3}x_i,\;Z\,\mathcal N^{-3}x_i\big\rangle-r\sum_i\big\langle\mathcal N^{-3}x_i,\;Z\,a_j^\dagger\mathcal N^{-3}x_i\big\rangle .
--   $$ The weak mean of $X$ in mode $j$ is $\mu_{r,j}(X)=\Lambda_{r,j}(X;1)$.
--
--   For every real $r$ and every mode $j$,
--
--   $$
--   \mu_{r,j}(X)=\sum_i\big\langle a_j\mathcal N^{-3}x_i,\;\mathcal N^{-3}x_i\big\rangle .
--   $$
--
--   In particular the weak mean does not depend on the thermal parameter $r$. Writing $\psi_i=\mathcal N^{-3}x_i$, so that $\rho=\sum_i|\psi_i\rangle\langle\psi_i|$, the right-hand side is the regularized form of $\sum_i\langle a_j\psi_i,\psi_i\rangle$, i.e. of the complex conjugate of the mean amplitude $\operatorname{Tr}(\rho\,a_j)$ of mode $j$. This value is the constant subtracted in the centered pairings.
--
--   **Formalization Note** The right-hand side is a `tsum`; the series converges absolutely since both families $(a_j\mathcal N^{-3}x_i)_i$ and $(\mathcal N^{-3}x_i)_i$ are square-summable. In Lean, $a_j\mathcal N^{-3}$ is `sandwich 0 3 _ j` and $a_j^\dagger\mathcal N^{-3}$ is `creationSandwich 0 3 _ j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean#L748-L762

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.WeightedColumns
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem OAI.EntropyPhotonNumber.WeightedColumns.weakMean_trace (r : ℝ) (j : Fin n) :
    X.weakMean r j=∑' i, inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i)) := by sorry
