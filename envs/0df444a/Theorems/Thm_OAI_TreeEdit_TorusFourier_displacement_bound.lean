-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusFourier_displacement_bound
-- name    : OAI.TreeEdit.TorusFourier.displacement_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:11:32.834008+00:00
-- url     : https://prove2.me/theorems/c2146bff-1844-4b8d-8cef-37348832b663
-- title:
--   Edit-Lipschitz maps into $\ell_1$ have small average displacement under diagonal shifts
-- statement:
--   This is the Fourier-analytic upper bound used in the lower bound for the $\ell_1$ distortion of edit distance: maps into $\ell_1$ that are Lipschitz for the edit distance of the random tree words have small average displacement under diagonal shifts.
--
--   **Configurations.** Fix natural numbers $g, s, L, T$ and put $m = gs$. Let $I$ be a type, $r : I \to \mathbb{N}$, and an injective map $j : \{0,\dots,g-1\} \to I$. For a permutation $\sigma$ of $I$ let $P(\sigma) = \prod_{v=0}^{g-1} r(\sigma(j(v)))$. A child index $i \in \{0,\dots,m-1\}$ belongs to the group $\gamma(i) = \lfloor i/s \rfloor$; write $p_i(\sigma) = r(\sigma(j(\gamma(i))))$ and, for $z \in \mathbb{Z}/L$ with standard representative $\bar z$, put $c_\sigma(z,i) = 1 + (\bar z \bmod p_i(\sigma))\cdot \lfloor P(\sigma)/p_i(\sigma)\rfloor$. A configuration of depth $0$ is trivial, and a configuration of depth $h+1$ is a tuple $C = (\sigma, (z_i, C_i)_{i<m})$ consisting of a permutation $\sigma$ of $I$, residues $z_i \in \mathbb{Z}/L$ and configurations $C_i$ of depth $h$.
--
--   **States.** For an abelian group $A$ let $\mathcal{S}_0(A) = A$ and $\mathcal{S}_{h+1}(A) = \mathcal{S}_h(A)^m$; an element of $\mathcal{S}_h(A)$ labels the $m^h$ leaves of the complete $m$-ary tree of depth $h$, and addition is coordinatewise. Let $\Delta_h(u) \in \mathcal{S}_h(A)$ be the constant state with every leaf equal to $u$.
--
--   **Sampled words.** Let $R \ge 1$ and $M \ge 1$. For $t \in \mathbb{R}/\mathbb{Z}$ with representative $\tilde t \in [0,1)$ put $\mathrm{bin}_R(t) = \lfloor R\tilde t\rfloor \in \{0,\dots,R-1\}$. For a configuration $C$ of depth $h$ and $x \in \mathcal{S}_h(\mathbb{R}/\mathbb{Z})$ the word $w_C(x)$, of length $(mT)^h$, is defined recursively: for $h=0$ it is the one-letter word $\mathrm{bin}_R(x)$; for $C = (\sigma,(z_i,C_i))$ of depth $h+1$ it is the concatenation, over rounds $a = 0,1,\dots,T-1$ and inside each round over $i = 0,\dots,m-1$, of the words $w_{C_i}\big(x_i + \Delta_h(a\,c_\sigma(z_i,i)/P(\sigma))\big)$, each letter being tagged with the child index $i$. For $x \in \mathcal{S}_h(\mathbb{Z}/M)$ the sampled word is $W_C(x) = w_C(x/M)$, where every leaf value $u \in \mathbb{Z}/M$ with standard representative $\bar u \in \{0,\dots,M-1\}$ is sent to $\bar u/M \bmod 1$. Finally $\mathrm{ed}$ denotes the unit-cost edit distance (the least number of single-letter insertions, deletions and substitutions), and $\mathbb{E}_x$ is the average over $x$ uniformly distributed in a finite group.
--
--   **Statement.** Assume that every $r(v)$ is prime and $r$ is injective; $M, R \ge 1$; $P(\sigma) \mid M$ and $P(\sigma) \le V$ for every permutation $\sigma$ of $I$, and $V \le T$; $D, Q > 0$ and $J$ are natural numbers with $M = RD$ and $M = JQ$; $b \ge 1$ with $r(v) \ge b$ for all $v \in I$, $Q \le b^e$, $e + K \le g$ and $K \ge 1$; and $(gs+1)Q < M$. Let $C$ be a configuration of depth $h$, let $t \in \mathbb{Z}/M$ and $a \ge 0$, and let $F : \mathcal{S}_h(\mathbb{Z}/M) \to \ell_1$ be a map into the space $\ell_1$ of absolutely summable real sequences such that $\|F(x) - F(y)\|_1 \le a\,\mathrm{ed}\big(W_C(x), W_C(y)\big)$ for all states $x, y$. Then
--
--   $$
--   \mathbb{E}_x\,\big\|F(x) - F\big(x + \Delta_h(t)\big)\big\|_1 \le 4a\,(gsT)^h\left(K^{-h} + h\Big(\frac{2R}{Q} + \frac{2V}{T}\Big)\right),
--   $$
--
--   where $x$ is uniformly distributed on $\mathcal{S}_h(\mathbb{Z}/M)$.
--
--   Thus an $a$-Lipschitz map moves a random state, on average, by only a small fraction of $a$ times the word length $(gsT)^h$ under any diagonal shift, as soon as $K^{-h}$ and the error terms $2R/Q$ and $2V/T$ are small. In the distortion lower bound this is played against the fact that suitable diagonal shifts produce sampled words at large edit distance.
--
--   **Formalization Note** The space $\ell_1$ is `RealL1` (Mathlib's `lp` space of exponent $1$ over the natural numbers) with its metric `dist`, and the average is `average` over `State (ZMod M) (g*s) h`. The type $I$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean#L274-L295

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum

open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

theorem OAI.TreeEdit.TorusFourier.displacement_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M) (C : Config I L (g*s) h) (t : ZMod M)
    (F : State (ZMod M) (g*s) h → RealL1) (a : ℝ) (ha : 0 ≤ a)
    (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (sampledWord r j T R h C x).val (sampledWord r j T R h C y).val) :
    average (fun x => dist (F x) (F (x + diagonal (A := ZMod M) (m := g*s) h t))) ≤
      a * FiniteTree.length (g*s) T h * (4*((K : ℝ)⁻¹^h + h*(2*(R : ℝ)/Q + 2*(V : ℝ)/T))) := by sorry
