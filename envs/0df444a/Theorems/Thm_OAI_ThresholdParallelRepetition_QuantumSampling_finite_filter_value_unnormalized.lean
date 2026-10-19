-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_finite_filter_value_unnormalized
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:55:43.478528+00:00
-- url     : https://prove2.me/theorems/a6e81dd0-683f-497d-9d8c-efef0e1f034f
-- title:
--   Locally filtered strategies, normalized by the probability that some filter succeeds, do not exceed the entangled value
-- statement:
--   Let $G$ be a two-player nonlocal game with finite question sets $\mathcal X,\mathcal Y$, finite answer sets $\mathcal A,\mathcal B$, a probability distribution $\pi$ on $\mathcal X\times\mathcal Y$ and an acceptance predicate $V(x,y,a,b)\in\{0,1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite-dimensional entangled strategies (a unit vector $\psi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ together with POVMs $(S^x_a)_{a\in\mathcal A}$ for Alice and $(T^y_b)_{b\in\mathcal B}$ for Bob), of the winning probability $\sum_{x,y}\pi(x,y)\sum_{a,b}V(x,y,a,b)\,\langle\psi,(S^x_a\otimes T^y_b)\psi\rangle$.
--
--   For finite index sets $m,n$ identify a matrix $C\in\mathbb{C}^{m\times n}$ with the (unnormalized) bipartite vector $\operatorname{vec}C=\sum_{i,j}C_{ij}\,e_i\otimes e_j\in\mathbb{C}^m\otimes\mathbb{C}^n$, write $\|C\|_2=\bigl(\sum_{i,j}|C_{ij}|^2\bigr)^{1/2}$ for its Hilbert–Schmidt norm, and for $S\in\mathbb{C}^{m\times m}$, $T\in\mathbb{C}^{n\times n}$ put $\langle S\otimes T\rangle_C=\operatorname{Re}\langle\operatorname{vec}C,(S\otimes T)\operatorname{vec}C\rangle=\operatorname{Re}\operatorname{tr}(C^*SCT^{\mathsf T})$. For POVMs $P=(P_a)_{a\in\mathcal A}$ on $\mathbb{C}^m$ and $Q=(Q_b)_{b\in\mathcal B}$ on $\mathbb{C}^n$ (positive semidefinite matrices summing to the identity) and a predicate $W:\mathcal A\times\mathcal B\to\{0,1\}$, the winning weight of $C$ is $\operatorname{win}_C(P,Q,W)=\sum_{(a,b):\,W(a,b)=1}\langle P_a\otimes Q_b\rangle_C$.
--
--   Let $m,n,p,q$ be finite index sets with $n$ and $q$ nonempty, and let $D\in\mathbb{C}^{n\times q}$ satisfy $\|D\|_2^2>0$. For each $x\in\mathcal X$ let $P^x$ be a POVM on $\mathbb{C}^m$ with outcomes in $\mathcal A$ and let $K_x\in\mathbb{C}^{m\times n}$ satisfy $K_x^*K_x\le I$; for each $y\in\mathcal Y$ let $Q^y$ be a POVM on $\mathbb{C}^p$ with outcomes in $\mathcal B$ and let $L_y\in\mathbb{C}^{p\times q}$ satisfy $L_y^*L_y\le I$. Then
--
--   $$
--   \sum_{(x,y)\in\mathcal X\times\mathcal Y}\pi(x,y)\,\frac{\operatorname{win}_{K_xDL_y^{\mathsf T}}\bigl(P^x,Q^y,V(x,y,\cdot,\cdot)\bigr)}{\|K_xD\|_2^2+\|DL_y^{\mathsf T}\|_2^2-\|K_xDL_y^{\mathsf T}\|_2^2}\;\le\;\omega^*(G).
--   $$
--
--   Think of $\operatorname{vec}D$ as an unnormalized shared state and of $K_x$, $L_y$ as local filters: Alice's filter succeeds with Kraus operator $K_x$ and fails with $(I-K_x^*K_x)^{1/2}$, and similarly for Bob. After division by $\|D\|_2^2$, the numerator is the probability that both filters succeed and the players then win with the measurements $P^x,Q^y$, while the denominator is the probability that at least one of the two filters succeeds. The theorem says that this post-selected ratio, averaged over the questions, never exceeds the entangled value. It is the basic tool for converting filtered (post-selected) strategies into upper bounds in terms of $\omega^*(G)$, for instance in quantum correlated-sampling arguments.
--
--   **Formalization Note** The question and answer sets are `Fin (x+1)`, `Fin (y+1)`, `Fin (a+1)`, `Fin (b+1)`; $\omega^*(G)$ is `entangledValue G`, the `sSup` of `successProbability G S` over strategies whose state lives on `Fin (dimA+1) × Fin (dimB+1)`. The index types $m$ and $p$ are arbitrary finite types. Each denominator is nonnegative, and if it vanishes then so does the corresponding numerator; Lean's convention $r/0=0$ makes such a term $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SamplingStrategy.lean#L410-L437

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_n u_A u_m u_ι u_p u_q u_B
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]
open Filter Topology

theorem OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
        (hsSq (K z.1*D) + hsSq (D*(L z.2)ᵀ) - hsSq (K z.1*D*(L z.2)ᵀ)))) ≤
      entangledValue G := by sorry
