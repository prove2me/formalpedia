-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusFourier_mass_bound
-- name    : OAI.TreeEdit.TorusFourier.mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:10:40.537246+00:00
-- url     : https://prove2.me/theorems/8ae4e7ae-ae47-476c-8253-dbbd12044377
-- title:
--   Spectral mass on the unit diagonal shift is at most $a(gsT)^h(K^{-h} + h(2R/Q + 2V/T))$
-- statement:
--   This is the central Fourier estimate for the random tree words used in the lower bound for the $\ell_1$ distortion of edit distance.
--
--   **Configurations.** Fix natural numbers $g, s, L, T$ and put $m = gs$. Let $I$ be a type, $r : I \to \mathbb{N}$, and an injective map $j : \{0,\dots,g-1\} \to I$. For a permutation $\sigma$ of $I$ let $P(\sigma) = \prod_{v=0}^{g-1} r(\sigma(j(v)))$. A child index $i \in \{0,\dots,m-1\}$ belongs to the group $\gamma(i) = \lfloor i/s \rfloor$; write $p_i(\sigma) = r(\sigma(j(\gamma(i))))$ and, for $z \in \mathbb{Z}/L$ with standard representative $\bar z$, put $c_\sigma(z,i) = 1 + (\bar z \bmod p_i(\sigma))\cdot \lfloor P(\sigma)/p_i(\sigma)\rfloor$. A configuration of depth $0$ is trivial, and a configuration of depth $h+1$ is a tuple $C = (\sigma, (z_i, C_i)_{i<m})$ consisting of a permutation $\sigma$ of $I$, residues $z_i \in \mathbb{Z}/L$ and configurations $C_i$ of depth $h$.
--
--   **States.** For an abelian group $A$ let $\mathcal{S}_0(A) = A$ and $\mathcal{S}_{h+1}(A) = \mathcal{S}_h(A)^m$; an element of $\mathcal{S}_h(A)$ labels the $m^h$ leaves of the complete $m$-ary tree of depth $h$, and addition is coordinatewise. Let $\Delta_h(u) \in \mathcal{S}_h(A)$ be the constant state with every leaf equal to $u$.
--
--   **Sampled words.** Let $R \ge 1$ and $M \ge 1$. For $t \in \mathbb{R}/\mathbb{Z}$ with representative $\tilde t \in [0,1)$ put $\mathrm{bin}_R(t) = \lfloor R\tilde t\rfloor \in \{0,\dots,R-1\}$. For a configuration $C$ of depth $h$ and $x \in \mathcal{S}_h(\mathbb{R}/\mathbb{Z})$ the word $w_C(x)$, of length $(mT)^h$, is defined recursively: for $h=0$ it is the one-letter word $\mathrm{bin}_R(x)$; for $C = (\sigma,(z_i,C_i))$ of depth $h+1$ it is the concatenation, over rounds $a = 0,1,\dots,T-1$ and inside each round over $i = 0,\dots,m-1$, of the words $w_{C_i}\big(x_i + \Delta_h(a\,c_\sigma(z_i,i)/P(\sigma))\big)$, each letter being tagged with the child index $i$. For $x \in \mathcal{S}_h(\mathbb{Z}/M)$ the sampled word is $W_C(x) = w_C(x/M)$, where every leaf value $u \in \mathbb{Z}/M$ with standard representative $\bar u \in \{0,\dots,M-1\}$ is sent to $\bar u/M \bmod 1$. Finally $\mathrm{ed}$ denotes the unit-cost edit distance (the least number of single-letter insertions, deletions and substitutions), and $\mathbb{E}_x$ is the average over $x$ uniformly distributed in a finite group.
--
--   **Spectral quantities.** Let $G = \mathcal{S}_h(\mathbb{Z}/M)$ and let $\widehat{G}$ be its set of additive characters (maps $\chi : G \to \mathbb{C}$ with $\chi(0)=1$ and $\chi(x+y)=\chi(x)\chi(y)$). For $H : \widehat{G} \to \mathbb{R}$ define the energy $\mathcal{E}_H(z) = \sum_{\chi\in\widehat G} |1-\chi(z)|^2 H(\chi)$ and the active mass $\mathcal{A}_H(w) = \sum_{\chi \in \widehat{G},\ \chi(w) \ne 1} H(\chi)$. Say that $H$ satisfies the spectral bound with constant $a$ for $C$ if $\mathcal{E}_H(z) \le a\,\mathbb{E}_x\,\mathrm{ed}\big(W_C(x), W_C(x+z)\big)$ for every $z \in G$, with $x$ uniform on $G$.
--
--   **Statement.** Assume that every $r(v)$ is prime and $r$ is injective; $M, R \ge 1$; $P(\sigma) \mid M$ and $P(\sigma) \le V$ for every permutation $\sigma$ of $I$, and $V \le T$; $D, Q > 0$ and $J$ are natural numbers with $M = RD$ and $M = JQ$; $b \ge 1$ with $r(v) \ge b$ for all $v \in I$, $Q \le b^e$, $e + K \le g$ and $K \ge 1$; and $(gs+1)Q < M$. Let $C$ be a configuration of depth $h$, let $H : \widehat{G} \to \mathbb{R}$ be nonnegative and $a \ge 0$, and suppose that $H$ satisfies the spectral bound with constant $a$ for $C$. Then
--
--   $$
--   \mathcal{A}_H\big(\Delta_h(1)\big) \le a\,(gsT)^h\left(K^{-h} + h\Big(\frac{2R}{Q} + \frac{2V}{T}\Big)\right).
--   $$
--
--   The left side is the total weight of the characters that are nontrivial on the unit diagonal shift. Measured against the word length $(gsT)^h$, the main term decays like $K^{-h}$, up to error terms coming from high diagonal frequencies ($2R/Q$) and from the cycle shifts of the nodes ($2V/T$). Together with the spectral representation of averaged $\ell_1$ displacements it shows that maps into $\ell_1$ that are Lipschitz for the edit distance of sampled words barely move under diagonal shifts.
--
--   **Formalization Note** The spectral bound is the predicate `SpectralBound`, the energy and active mass are `energy` and `activeMass`, and $K^{-h}$ is the $h$-th power of the real inverse of $K$. The type $I$ need not be finite, and the embedding $j$ is coerced to a function wherever $P(\sigma)$ and the words are formed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean#L185-L254

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

theorem OAI.TreeEdit.TorusFourier.mass_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M)
    (C : Config I L (g*s) h) (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hbound : SpectralBound (R := R) r j T h C H a) :
    activeMass H (diagonal (A := ZMod M) (m := g*s) h 1) ≤
      a * FiniteTree.length (g*s) T h * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) := by sorry
