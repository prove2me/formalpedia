-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_sampled_separation
-- name    : OAI.TreeEdit.TorusTree.sampled_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:59.264717+00:00
-- url     : https://prove2.me/theorems/256bfb9b-ed8a-4e6e-b970-86fd1b5f0646
-- title:
--   Half-turn separation of grid-sampled circle-tree words
-- statement:
--   Fix an integer $k\ge 2$ and put $m=16k^3$, $T=k^{52k}$ and $R=k^{8k}$. Let $\mathcal P_k$ be the set of primes $p$ with $k^2<p\le k^3$, let $L=\prod_{p\in\mathcal P_k}p$, and let $j:\{0,1,\dots,16k-1\}\to\mathcal P_k$ be an injective map. For a permutation $\sigma$ of $\mathcal P_k$ let $\pi_\sigma=\prod_{u=0}^{16k-1}\sigma(j(u))$ be the product of the $16k$ distinct primes selected by $\sigma\circ j$. Let $Q=k^{12k}$ and let
--   $$
--   M=R\cdot 2Q\,\big((m+1)Q+1\big)\prod_{\sigma\in\mathrm{Sym}(\mathcal P_k)}\pi_\sigma
--   $$
--   be the fine modulus (a positive even integer).
--
--   *Configurations.* Let $\mathcal C_0$ be a one-point set and $\mathcal C_{h+1}=\mathrm{Sym}(\mathcal P_k)\times(\mathbb Z/L\mathbb Z\times\mathcal C_h)^m$. For $C=(\sigma,(z_i,C_i)_{i<m})\in\mathcal C_{h+1}$ and a child index $i<m$ put $p_i=\sigma\big(j(\lfloor i/k^2\rfloor)\big)$ and
--   $$
--   c_i=1+(\bar z_i\bmod p_i)\cdot\frac{\pi_\sigma}{p_i},
--   $$
--   where $\bar z_i\in\{0,\dots,L-1\}$ is the representative of $z_i$.
--
--   *Good configurations.* For $t\in\mathbb R/\mathbb Z$ let $\|t\|$ be the distance from $t$ to the nearest integer. For $C\in\mathcal C_0$, $\mathrm{Good}_0(C,t)$ means $\|t\|\ge 1/R$. For $C=(\sigma,(z_i,C_i)_{i<m})\in\mathcal C_{h+1}$, $\mathrm{Good}_{h+1}(C,t)$ means that for every $a\in\{0,1,\dots,\pi_\sigma-1\}$
--   $$
--   m\le 64\cdot\#\Big\{i<m:\ \mathrm{Good}_h\Big(C_i,\ t+\frac{a\,c_i}{\pi_\sigma}\Big)\Big\},
--   $$
--   i.e. at least a $1/64$ fraction of the children are good at the correspondingly rotated point.
--
--   *States and words.* For an abelian group $G$ let $\mathcal S_0(G)=G$ and $\mathcal S_{h+1}(G)=\mathcal S_h(G)^m$ with coordinatewise addition (a state of depth $h$ labels the leaves of the complete $m$-ary tree of depth $h$ by elements of $G$), and let $\Delta_h(g)$ be the constant state all of whose leaves equal $g$. Let $\Sigma_0=\{0,\dots,R-1\}$ and $\Sigma_{h+1}=\{0,\dots,m-1\}\times\Sigma_h$. For $C\in\mathcal C_h$ and $x\in\mathcal S_h(\mathbb R/\mathbb Z)$ the word $w_h(C,x)$ over $\Sigma_h$, of length $(mT)^h$, is defined recursively: $w_0(C,x)$ is the one-letter word $\lfloor R\{x\}\rfloor$, where $\{x\}\in[0,1)$ is the representative of $x$; and for $C=(\sigma,(z_i,C_i)_{i<m})$, $w_{h+1}(C,x)$ is the concatenation, over $a=0,\dots,T-1$ (outer loop) and $i=0,\dots,m-1$ (inner loop), of the word $w_h\big(C_i,\ x_i+\Delta_h(a c_i/\pi_\sigma)\big)$ with every letter $\ell$ replaced by $(i,\ell)$.
--
--   *Sampled words and deficit.* For $C\in\mathcal C_k$ and $x\in\mathcal S_k(\mathbb Z/M\mathbb Z)$ let $\tilde w(x)=w_k(C,\iota(x))$, where $\iota$ applies the homomorphism $\mathbb Z/M\mathbb Z\to\mathbb R/\mathbb Z$, $r\mapsto r/M \bmod 1$, at every leaf. For words $u,v$ let $\operatorname{def}(u,v)=|u|-\operatorname{LCS}(u,v)$, where $\operatorname{LCS}(u,v)$ is the length of a longest (not necessarily contiguous) common subsequence.
--
--   **Theorem.** Let $C\in\mathcal C_k$ satisfy $\mathrm{Good}_k(C,\tfrac12)$. Then for every $x\in\mathcal S_k(\mathbb Z/M\mathbb Z)$
--   $$
--   (mT)^k\le 128^k\cdot\operatorname{def}\Big(\tilde w(x),\ \tilde w\big(x+\Delta_k(M/2)\big)\Big).
--   $$
--
--   Since $(mT)^k$ is the common length of the two words, this says that shifting every leaf of the grid state by half a turn destroys at least a $128^{-k}$ fraction of every common subsequence, uniformly over the finite group $\mathcal S_k(\mathbb Z/M\mathbb Z)$. This is the separation input that, after binary encoding, is fed into the transfer to an $\ell_1$-distortion lower bound.
--
--   **Formalization Note** The configuration is `C : Config (Pool k) (residueModulus k) (branching k) k`, the hypothesis is `Good (resolution k)⁻¹ poolPrime j k C (point 2)` with `point 2` the class of $1/2$ in `UnitAddCircle`, and $\tilde w$ is `sampledWord poolPrime j (repetitions k) (resolution k) k C`. The left side is `FiniteTree.length (branching k) (repetitions k) k`, defined by $N_0=1$, $N_{h+1}=T\,(m\,N_h)$, which equals $(mT)^k$. The shift is the diagonal of the natural number `fineModulus j / 2` (exact, since $M$ is even). The `NeZero` instance arguments for $M$ and $R$ are automatically satisfied.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean#L214-L240

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

theorem OAI.TreeEdit.TorusTree.sampled_separation {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    [NeZero (fineModulus j)] [NeZero (resolution k)]
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2))
    (x : State (ZMod (fineModulus j)) (branching k) k) :
    FiniteTree.length (branching k) (repetitions k) k ≤ 128^k * deficit
      (sampledWord poolPrime j (repetitions k) (resolution k) k C x).val
      (sampledWord poolPrime j (repetitions k) (resolution k) k C
        (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ))).val := by sorry
