-- Prove2me | Theorems.Thm_LatticePrepro_exists_latticeReduction
-- name    : LatticePrepro.exists_latticeReduction
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:33.7092+00:00
-- url     : https://prove2.me/theorems/b109f3ec-b0b9-48fa-bc8a-ee4b51abe491
-- title:
--   Lemma 3.12 — fixed lattices from block-sparse linear systems
-- statement:
--   Let $\mathsf p$ be a prime and $L$ a linear-system family over $\mathbb F_{\mathsf p}$ with instance set $X$: a fixed linear map $A$ on $\mathbb F_{\mathsf p}^{\iota}$, right-hand sides $b_x$ ($x\in X$), and $n=|\iota|$ columns partitioned into $D$ blocks of size $Q$ each. Let $g\in\mathbb N$ with $g<Q$, assume $D\ge1$, and let $p$ be a norm exponent, a real number $p\ge1$ or $p=\infty$, with $s=\min\{p,2\}$ ($s=2$ for $p=\infty$). Then there exist
--
--   - a lattice $\Lambda\subseteq\mathbb Z^M$ (an additive subgroup), the same for every instance, with $2n\le M<4n$ and $N\cdot\mathbb Z^M\subseteq\Lambda$ for some integer $N>0$, so that $\Lambda$ has full rank;
--   - an integer target $t_x\in\mathbb Z^M$ for every instance $x$;
--   - an integer radius $R$ with $1\le R\le M$, the same for every instance;
--   - a residual weight $w(x,v)\in\mathbb N$ for every instance $x$ and every $v\in\mathbb Z^M$,
--
--   such that:
--
--   1. **YES instances.** If $Au=b_x$ has a solution $u\in\{0,1\}^{\iota}$ with at most one nonzero coordinate per block, then $\|t_x-v\|_p\le R$ for some $v\in\Lambda$.
--   2. **Weight bound.** For every instance $x$ and every $v\in\Lambda$,
--   $$w(x,v)\le16\cdot D\cdot\left(\frac{\|t_x-v\|_p}{R}\right)^{s}.$$
--   3. **NO instances.** If every solution $u$ of $Au=b_x$ has Hamming weight greater than $g\cdot D$, then $w(x,v)>g\cdot D$ for every $v\in\Lambda$.
--
--   Parts 2 and 3 give $\|t_x-v\|_p>(g/16)^{1/s}R$ for all $v\in\Lambda$ on NO instances, so for $g>16f^s$ the instances are $f$-gap CVPP instances; this is how the paper phrases Lemma 3.12. It is the lattice half of the conversions: composed with the moment reduction (Theorem 4.8) it gives Theorem 5.1 for lattices, and the residual weight is the quantity tested in Lemma 5.2.
--
--   **Formalization Note.** The conclusion is `Nonempty (LatticeReduction L g pn)`, i.e. such data exists; the structure `LatticeReduction` packages the lattice family $(\Lambda,(t_x))$, $R$, $N$ and $w$ with the properties above. The lattice is a $\mathbb Z$-submodule of $\mathbb Z^M$ (`Submodule ℤ (M → ℤ)`), and full rank is encoded by $N\cdot\mathbb Z^M\subseteq\Lambda$. The norm exponent is a `PNorm`, so every real $p\ge1$ and $p=\infty$ are covered, whereas the paper states the lemma for rational $p$ (needed only for computability). The hypotheses $g<Q$ (`L.blockSize`) and $D\ge1$ (`L.numBlocks`) correspond to $Q>\Gamma$ and $D\ge1$ in Definition 3.10; Lean's gap $g$ is the paper's $\Gamma$. The polynomial-time claims (integer basis, membership test, computing $w$) are not formalized, and $w$ is an arbitrary function.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Conversions/Lattices.lean, LatticePrepro.exists_latticeReduction

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro

theorem LatticePrepro.exists_latticeReduction {p : ℕ} [Fact p.Prime] {X : Type}
    (L : LinearSystemFamily (ZMod p) X) {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) : Nonempty (LatticeReduction L g pn) := by sorry
