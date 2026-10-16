-- Prove2me | Theorems.Thm_OAI_GAD_kraus_complete
-- name    : OAI.GAD.kraus_complete
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:03:27.309861+00:00
-- url     : https://prove2.me/theorems/ba868bcd-d007-4bc9-9b09-bc03dc7a7689
-- title:
--   Completeness relation for the generalized amplitude-damping Kraus operators
-- statement:
--   Let $\gamma,\nu\in[0,1]$ and let $K_0,K_1,K_2,K_3$ be the Kraus matrices of the single-qubit generalized amplitude-damping channel, written in the basis $|0\rangle,|1\rangle$:
--
--   $$K_0=\sqrt{1-\nu}\begin{pmatrix}1&0\\0&\sqrt{1-\gamma}\end{pmatrix},\quad K_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},\quad K_2=\sqrt{\nu}\begin{pmatrix}\sqrt{1-\gamma}&0\\0&1\end{pmatrix},\quad K_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix},$$
--
--   Then, with $K_r^{*}$ the conjugate transpose and $I_2$ the $2\times2$ identity matrix,
--
--   $$
--   \sum_{r=0}^{3}K_r^{*}K_r=I_2 .
--   $$
--
--   Equivalently, the completely positive map $P\mapsto\sum_rK_rPK_r^{*}$ preserves the trace, so it is a quantum channel, and the same holds for its $n$-fold tensor power. The relation is used whenever one needs the channel to map density matrices to density matrices.
--
--   **Formalization Note** The Kraus matrices are `kraus γ ν r` for `r : Fin 4`, and the identity is stated as `∑ r, (kraus γ ν r).conjTranspose * kraus γ ν r = 1`. The hypotheses $\gamma,\nu\in[0,1]$ make all square roots real square roots of nonnegative numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Channel.lean#L61-L77

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.kraus_complete (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) :
    ∑ r, (kraus γ ν r).conjTranspose * kraus γ ν r = 1 := by sorry
