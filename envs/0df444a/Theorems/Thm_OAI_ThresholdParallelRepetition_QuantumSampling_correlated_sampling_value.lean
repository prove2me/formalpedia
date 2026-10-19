-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_correlated_sampling_value
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:56:58.081533+00:00
-- url     : https://prove2.me/theorems/9d91239c-b51f-4306-821e-45ac924a346b
-- title:
--   Question-dependent shared states that agree on average cannot beat the entangled value by much
-- statement:
--   Let $G$ be a two-player nonlocal game with finite question sets $\mathcal X,\mathcal Y$, finite answer sets $\mathcal A,\mathcal B$, a probability distribution $\pi$ on $\mathcal X\times\mathcal Y$ and an acceptance predicate $V(x,y,a,b)\in\{0,1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite-dimensional entangled strategies (a unit vector $\psi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ together with POVMs $(S^x_a)_{a\in\mathcal A}$ for Alice and $(T^y_b)_{b\in\mathcal B}$ for Bob), of the winning probability $\sum_{x,y}\pi(x,y)\sum_{a,b}V(x,y,a,b)\,\langle\psi,(S^x_a\otimes T^y_b)\psi\rangle$.
--
--   For finite index sets $m,n$ identify a matrix $C\in\mathbb{C}^{m\times n}$ with the (unnormalized) bipartite vector $\operatorname{vec}C=\sum_{i,j}C_{ij}\,e_i\otimes e_j\in\mathbb{C}^m\otimes\mathbb{C}^n$, write $\|C\|_2=\bigl(\sum_{i,j}|C_{ij}|^2\bigr)^{1/2}$ for its Hilbert–Schmidt norm, and for $S\in\mathbb{C}^{m\times m}$, $T\in\mathbb{C}^{n\times n}$ put $\langle S\otimes T\rangle_C=\operatorname{Re}\langle\operatorname{vec}C,(S\otimes T)\operatorname{vec}C\rangle=\operatorname{Re}\operatorname{tr}(C^*SCT^{\mathsf T})$. For POVMs $P=(P_a)_{a\in\mathcal A}$ on $\mathbb{C}^m$ and $Q=(Q_b)_{b\in\mathcal B}$ on $\mathbb{C}^n$ (positive semidefinite matrices summing to the identity) and a predicate $W:\mathcal A\times\mathcal B\to\{0,1\}$, the winning weight of $C$ is $\operatorname{win}_C(P,Q,W)=\sum_{(a,b):\,W(a,b)=1}\langle P_a\otimes Q_b\rangle_C$.
--
--   Let $n$ be a nonempty finite index set. For each Alice question $x\in\mathcal X$ let $M_x\in\mathbb{C}^{n\times n}$ with $\|M_x\|_2=1$ and let $P^x$ be a POVM on $\mathbb{C}^n$ with outcomes in $\mathcal A$; for each Bob question $y\in\mathcal Y$ let $N_y\in\mathbb{C}^{n\times n}$ with $\|N_y\|_2=1$ and let $Q^y$ be a POVM on $\mathbb{C}^n$ with outcomes in $\mathcal B$. Then for every $\varepsilon$ with $0<\varepsilon\le1$,
--
--   $$
--   \sum_{x,y}\pi(x,y)\,\operatorname{win}_{M_x}\bigl(P^x,Q^y,V(x,y,\cdot,\cdot)\bigr)\;\le\;\omega^*(G)+4\sqrt{2\varepsilon^2+\frac{12}{\varepsilon}\sqrt{2\sum_{x,y}\pi(x,y)\,\|M_x-N_y\|_2^2}} .
--   $$
--
--   The left-hand side is the winning probability of a fictitious strategy in which the shared state $\operatorname{vec}M_x$ may depend on Alice's question, while Bob only holds a guess $N_y$ depending on his own question. The theorem says that if the two descriptions agree on average, i.e. $\Delta=\sum_{x,y}\pi(x,y)\|M_x-N_y\|_2^2$ is small, then such a strategy is no better than an honest entangled strategy up to an error controlled by $\Delta$; for example, if $0<\Delta\le1$, the choice $\varepsilon=\Delta^{1/6}$ bounds the error term by $4\sqrt{2+12\sqrt2}\,\Delta^{1/6}$. This is a quantum correlated-sampling estimate for nonlocal games.
--
--   **Formalization Note** The question and answer sets are `Fin (x+1)`, `Fin (y+1)`, `Fin (a+1)`, `Fin (b+1)`, $\omega^*(G)$ is `entangledValue G`, $\|\cdot\|_2^2$ is `hsSq`, and $\operatorname{win}_{M_x}(P^x,Q^y,V(x,y,\cdot,\cdot))$ is `payoff (M x) (P x) (Q y) (G.accepts x y)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean#L301-L378

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_m u_n u_A u_B u_p u_ι
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix

theorem OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix n n ℂ) (N : Fin (y+1) → Matrix n n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM n (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by sorry
