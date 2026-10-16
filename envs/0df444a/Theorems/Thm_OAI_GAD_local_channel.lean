-- Prove2me | Theorems.Thm_OAI_GAD_local_channel
-- name    : OAI.GAD.local_channel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:03:00.513122+00:00
-- url     : https://prove2.me/theorems/ff8e6a58-a15d-4e33-a539-54d6cea82597
-- title:
--   Action of the single-qubit generalized amplitude-damping channel on a $2\times2$ matrix
-- statement:
--   Let $\gamma,\nu\in[0,1]$. The single-qubit generalized amplitude-damping channel with damping parameter $\gamma$ and environment parameter $\nu$ is given, in the basis $|0\rangle,|1\rangle$, by the four Kraus matrices
--
--   $$K_0=\sqrt{1-\nu}\begin{pmatrix}1&0\\0&\sqrt{1-\gamma}\end{pmatrix},\quad K_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},\quad K_2=\sqrt{\nu}\begin{pmatrix}\sqrt{1-\gamma}&0\\0&1\end{pmatrix},\quad K_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix},$$
--
--   and acts by $\mathcal N_{\gamma,\nu}(P)=\sum_{r=0}^{3}K_rPK_r^{*}$, where $K_r^{*}$ is the conjugate transpose. The theorem computes this action explicitly: for every complex $2\times2$ matrix $P=(P_{ab})_{a,b\in\{0,1\}}$,
--
--   $$
--   \mathcal N_{\gamma,\nu}(P)=\begin{pmatrix}(1-\gamma\nu)P_{00}+\gamma(1-\nu)P_{11} & \sqrt{1-\gamma}\,P_{01}\\ \sqrt{1-\gamma}\,P_{10} & \gamma\nu P_{00}+\bigl(1-\gamma(1-\nu)\bigr)P_{11}\end{pmatrix}.
--   $$
--
--   Thus the channel mixes the diagonal entries (populations) by a column-stochastic $2\times2$ matrix and multiplies the off-diagonal entries (coherences) by $\sqrt{1-\gamma}$. This closed form is the basic computational tool for the single-site output states, their spectra and entropies in the analysis of the channel.
--
--   **Formalization Note** $P$ is an arbitrary complex matrix, not necessarily a state. The Kraus matrices are `kraus γ ν r` for `r : Fin 4` and the map is `applyKraus (kraus γ ν) P`; the hypotheses $\gamma,\nu\in[0,1]$ guarantee that every square root is taken of a nonnegative number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Channel.lean#L39-L59

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.local_channel (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    applyKraus (kraus γ ν) P =
      !![((1-γ*ν:ℝ):ℂ)*P 0 0+((γ*(1-ν):ℝ):ℂ)*P 1 1,
         (Real.sqrt (1-γ):ℂ)*P 0 1;
         (Real.sqrt (1-γ):ℂ)*P 1 0,
         ((γ*ν:ℝ):ℂ)*P 0 0+((1-γ*(1-ν):ℝ):ℂ)*P 1 1] := by sorry
