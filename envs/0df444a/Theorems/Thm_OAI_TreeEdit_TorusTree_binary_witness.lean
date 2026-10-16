-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_binary_witness
-- name    : OAI.TreeEdit.TorusTree.binary_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:23:04.642412+00:00
-- url     : https://prove2.me/theorems/d2bb9e50-a489-4c54-b9f1-b1b9d00380e5
-- title:
--   A good circle-tree configuration yields binary strings of $\ell_1$-distortion at least $(k/128)^k/(1286400k^2)$
-- statement:
--   Fix an integer $k\ge 2$ and put $m=16k^3$, $T=k^{52k}$ and $R=k^{8k}$. Let $\mathcal P_k$ be the set of primes $p$ with $k^2<p\le k^3$, let $L=\prod_{p\in\mathcal P_k}p$, and let $j:\{0,1,\dots,16k-1\}\to\mathcal P_k$ be an injective map. For a permutation $\sigma$ of $\mathcal P_k$ let $\pi_\sigma=\prod_{u=0}^{16k-1}\sigma(j(u))$ be the product of the $16k$ distinct primes selected by $\sigma\circ j$.
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
--   For finite words $u,v$ over an alphabet, $\operatorname{ed}(u,v)$ is the edit distance: the least number of single-symbol insertions, deletions or substitutions (at any position, with no restriction on intermediate lengths) turning $u$ into $v$. Let $\ell_1=\ell_1(\mathbb N)$ be the real Banach space of absolutely summable sequences with metric $\|F-G\|_1$. For a finite set $W$ of binary strings and a map $f:W\to\ell_1$ the distortion is
--   $$
--   \operatorname{dist}(f)=\max_{u\ne v}\frac{\|f(u)-f(v)\|_1}{\operatorname{ed}(u,v)}\cdot\max_{u\ne v}\frac{\operatorname{ed}(u,v)}{\|f(u)-f(v)\|_1}
--   $$
--   (maxima over distinct $u,v\in W$), and $c_1(W)=\inf\{\operatorname{dist}(f): f:W\to\ell_1\ \text{injective}\}$ is the least $\ell_1$-distortion of $W$ under edit distance. Finally let $B_k=2\lceil\log_2(m^kR)\rceil+3$, where $\lceil\log_2 n\rceil$ is the least $e\ge0$ with $n\le 2^e$, and let $n_k=(mT)^k\,B_k$.
--
--   **Theorem.** Let $C\in\mathcal C_k$ satisfy $\mathrm{Good}_k(C,\tfrac12)$. Then there is a finite set $W$ of binary strings with $|W|\ge 2$, all of length exactly $n_k$, such that
--   $$
--   c_1(W)\ge\frac{(k/128)^k}{1286400\,k^2}.
--   $$
--
--   This is the single-scale witness of the edit-distance lower bound: whenever a good configuration exists at scale $k$ (which is established separately for all large $k$), there is a set of binary strings of length $n_k\le k^{60k^2}$ whose edit metric needs $\ell_1$-distortion at least of order $(k/128)^k$. Comparing this with the length then gives the stretched-exponential bound $\exp\big(c\sqrt{\log d\,\log\log d}\big)$ for strings of length at most $d$.
--
--   **Formalization Note** In Lean, $m,T,R,L$ are `branching k`, `repetitions k`, `resolution k`, `residueModulus k`; the configuration is `C : Config (Pool k) (residueModulus k) (branching k) k`; the hypothesis is `Good (resolution k)⁻¹ poolPrime j k C (point 2)`, where `point 2` is $1/2$ in `UnitAddCircle`; and $n_k$ is `binaryLength k = wordLength k * binaryWidth k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean#L21-L95

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer
import Definitions.Def_OAI_Combinatorics_TreeEdit_TorusLowerBound

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

theorem OAI.TreeEdit.TorusTree.binary_witness {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2)) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = binaryLength k) ∧
      ((k : ℝ)/128)^k / (1286400*(k : ℝ)^2) ≤ c1 W := by sorry
