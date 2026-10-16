-- Prove2me | Theorems.Thm_OAI_QuantumTrace_gibbs_high_moment_summable
-- name    : OAI.QuantumTrace.gibbs_high_moment_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:03:13.089676+00:00
-- url     : https://prove2.me/theorems/c9db53bd-be62-4df1-8bbe-56ac18233b02
-- title:
--   Heat-weighted squares are summable under an affine-plus-square-root bound
-- statement:
--   Let $J$ be an index set, let $u:J\to\mathbb{R}$ with $u_j\ge 0$, and let $k>0$ and $b\ge 0$. Let $z:J\to\mathbb{R}$ satisfy $z_j\ge 0$ and
--   $$z_j\le\frac{1}{k}\Big(u_j+b\sqrt{u_j/k}\Big)\qquad\text{for all } j .$$
--   If $\sum_je^{-u_j/2}$ converges, then
--   $$\sum_{j\in J}e^{-u_j}\,z_j^2<\infty .$$
--
--   The hypothesis on $z_j$ has exactly the form of the norm bound $\|z\|\le k^{-1}(u+\|B\|\sqrt{u/k})$ for eigenvectors of a regularized Gibbs inverse, with $b=\|B\|$. The theorem therefore turns such per-eigenvector bounds into summability of the Gibbs-weighted sum of their squares.
--
--   **Formalization Note** Summability is unconditional summability (`Summable`) of real families.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1528-L1561

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
variable {ι J : Type*}

theorem OAI.QuantumTrace.gibbs_high_moment_summable (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    {k b : ℝ} (hk : 0 < k) (hb : 0 ≤ b) (z : J → ℝ)
    (hz0 : ∀ j, 0 ≤ z j)
    (hz : ∀ j, z j ≤ k⁻¹*(u j+b*Real.sqrt (u j/k)))
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*z j^2) := by sorry
