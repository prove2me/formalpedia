-- Prove2me | Theorems.Thm_OAI_HoneycombForce_partition_split
-- name    : OAI.HoneycombForce.partition_split
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:30:32.864869+00:00
-- url     : https://prove2.me/theorems/1dadbcaa-071b-4c76-b49c-a093d67d6f84
-- title:
--   Splitting inequality for the tilted self-avoiding-walk partition function on the honeycomb lattice
-- statement:
--   Consider the honeycomb lattice with vertices $v=(i,j,\tau)$, $i,j\in\mathbb{Z}$, $\tau\in\{\uparrow,\downarrow\}$, placed in the plane $\mathbb{C}$ at the centroids of the triangles of the unit triangular lattice,
--
--   $$
--   x_{(i,j,\uparrow)}=i+\tfrac{j}{2}+\tfrac12+\mathrm{i}\,\tfrac{\sqrt3}{2}\bigl(j+\tfrac13\bigr),\qquad x_{(i,j,\downarrow)}=i+\tfrac{j}{2}+1+\mathrm{i}\,\tfrac{\sqrt3}{2}\bigl(j+\tfrac23\bigr),
--   $$
--
--   where the up vertex $(i,j,\uparrow)$ is adjacent to the three down vertices $(i,j-1,\downarrow)$, $(i,j,\downarrow)$, $(i-1,j,\downarrow)$. For a vertex $v$ and $k\in\mathbb{N}$ let $\mathrm{SAW}_k(v)$ be the finite set of $k$-step self-avoiding walks from $v$, i.e. sequences $\gamma=(\gamma_0,\dots,\gamma_k)$ of pairwise distinct vertices with $\gamma_0=v$ and $\gamma_l$ adjacent to $\gamma_{l+1}$ for $0\le l<k$, and write $\operatorname{end}(\gamma)=\gamma_k$. Fix a direction $e\in\mathbb{C}$ and a force $s\in\mathbb{R}$, put $\langle e,w\rangle=\operatorname{Re}(\bar e\,w)$ for $w\in\mathbb{C}$ and $\rho=1/\sqrt{2+\sqrt2}$, and define the tilted partition function
--
--   $$
--   Z_k(v)=\sum_{\gamma\in\mathrm{SAW}_k(v)}\rho^{k}\exp\bigl(s\,\langle e,\,x_{\operatorname{end}(\gamma)}-x_v\rangle\bigr).
--   $$
--
--   **Theorem.** For every vertex $o$, every $e\in\mathbb{C}$, every $s\in\mathbb{R}$ and all $n,m\in\mathbb{N}$,
--
--   $$
--   Z_{n+m}(o)\ \le\ \sum_{p\in\mathrm{SAW}_n(o)}\rho^{n}\exp\bigl(s\,\langle e,\,x_{\operatorname{end}(p)}-x_o\rangle\bigr)\,Z_m\bigl(\operatorname{end}(p)\bigr).
--   $$
--
--   The right-hand side is the total weight of all pairs consisting of an $n$-step self-avoiding walk $p$ from $o$ followed by an $m$-step self-avoiding walk started at the endpoint of $p$, whether or not the concatenation is self-avoiding; this is why only an inequality holds. It is the submultiplicativity input for the existence of the fixed-length free energy $\lim_{n\to\infty}\frac1n\log Z_n(o)$: bounding each $Z_m(\operatorname{end}(p))$ by $\sup_v Z_m(v)$ gives $Z_{n+m}(o)\le Z_n(o)\cdot\sup_v Z_m(v)$, so the logarithm of the partition function maximized over starting vertices is subadditive in the length.
--
--   **Formalization Note** Vertices are records `Vertex` with fields `col`, `row`, `up`, and positions are `position`. Walks are lists of $k+1$ vertices, `saws o k` is the finset of $k$-step self-avoiding walks from `o`, `endpoint o p` is the last entry of `p` (the default `o` is never used since walks are nonempty), `displacement o p` is `position (endpoint o p) - position o`, and `projection e w` is `(star e * w).re`. The partition function is `partition o e s k`, which includes the factor $\rho^k$. The vector $e$ need not have modulus $1$, and $s$ may have either sign.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Honeycomb/FreeEnergy.lean#L504-L534

import Mathlib
import Definitions.Def_HoneycombFreeEnergy
import Definitions.Def_OAI_Probability_Honeycomb_FreeEnergy

open OAI OAI.HoneycombForce
open scoped ENNReal Topology
open Filter

theorem OAI.HoneycombForce.partition_split (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n+m) ≤ ∑ p ∈ saws o n,
      (rho ^ n * Real.exp (s * projection e (displacement o p))) *
        partition (endpoint o p) e s m := by sorry
