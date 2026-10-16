-- Prove2me | Theorems.Thm_OAI_Annihilation_diagonal_mode_left
-- name    : OAI.Annihilation.diagonal_mode_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:47.017688+00:00
-- url     : https://prove2.me/theorems/01d9d975-ae10-4bae-916e-63f665053478
-- title:
--   Quadratic form of a weighted diagonal operator against a mode-number multiplier
-- statement:
--   Let $\mathcal F_n=\ell^2(\mathbb N^n;\mathbb C)$, write $|k|=k_1+\dots+k_n$ for $k\in\mathbb N^n$, and let $\mathcal N^{-1}$ be multiplication by $(1+|k|)^{-1}$. Let $f:\mathbb N^n\to\mathbb R$ and $C\ge0$ be such that $\big|f(k)/(1+|k|)^4\big|\le C$ for all $k$, and let $D_f$ be the bounded multiplication operator $(D_fx)(k)=\frac{f(k)}{(1+|k|)^4}x(k)$. For a mode $j$ and $u\in\{0,1\}$ let $M_{j,u}$ be multiplication by $\frac{k_j+u}{1+|k|}$. Then for every $x\in\mathcal F_n$ the series below converges and
--
--   $$
--   \sum_{k\in\mathbb N^n}\frac{(k_j+u)\,f(k)}{(1+|k|)^6}\,|x(k)|^2=\operatorname{Re}\big\langle\mathcal N^{-1}x,\;D_f\,M_{j,u}\,x\big\rangle .
--   $$
--
--   This is a bookkeeping identity for the weak form of the thermal generator tested against diagonal observables: the "mode" terms of the generator pairing, which involve $\mathcal N^{-1}$ and the mode multipliers $k_j/(1+|k|)$ and $(k_j+1)/(1+|k|)$, reduce to explicit weighted sums over the number basis.
--
--   **Formalization Note** The parameter $u$ is a Boolean (`true` corresponds to $u=1$). $D_f$ is `Annihilation.diagonal` applied to $k\mapsto f(k)/(1+|k|)^4$, $M_{j,u}$ is `modeBound j u`, and the conclusion is a `HasSum` statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L91-L108

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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy

open OAI OAI.Annihilation
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.Annihilation.diagonal_mode_left (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (u : Bool) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (inverseWeight 1 x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x))).re := by sorry
