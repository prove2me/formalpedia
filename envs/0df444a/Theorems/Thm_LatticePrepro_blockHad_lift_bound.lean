-- Prove2me | Theorems.Thm_LatticePrepro_blockHad_lift_bound
-- name    : LatticePrepro.blockHad_lift_bound
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:33.149435+00:00
-- url     : https://prove2.me/theorems/b8480cfe-3cc8-4695-91d5-c0715027bafc
-- title:
--   Hadamard image of a block-sparse binary vector (proof of Lemma B.2, YES case)
-- statement:
--   Let $\mathsf p$ be a prime, $\beta$ a finite set of block indices and $k\in\mathbb N$, and consider vectors indexed by $\beta\times\mathbb F_2^k$, cut into the blocks $\{s\}\times\mathbb F_2^k$ of size $2^k$. Let $e\in\mathbb F_{\mathsf p}^{\beta\times\mathbb F_2^k}$ be binary (every coordinate is $0$ or $1$) with at most one nonzero coordinate in each block. Let $\tilde e\in\mathbb Z^{\beta\times\mathbb F_2^k}$ be its integer lift (a $\{0,1\}$-vector) and $\mathcal H$ the block Hadamard map, $(\mathcal Hv)_{(s,u)}=\sum_{w}(-1)^{\langle u,w\rangle}v_{(s,w)}$. Then
--   $$\bigl|(\mathcal H\tilde e)_{(s,u)}\bigr|\le1\ \text{ for all }(s,u),\qquad \bigl|\{(s,u):(\mathcal H\tilde e)_{(s,u)}\neq0\}\bigr|\le\operatorname{wt}(e)\cdot2^k,$$
--   where $\operatorname{wt}(e)$ is the number of nonzero coordinates of $e$.
--
--   This is the YES-instance step in the proof of Lemma B.2 (Hadamard blocks): each nonzero block of $e$ is mapped to a column of the Hadamard matrix, with entries $\pm1$. In the lattice reduction of Lemma 3.12 for $2<p\le\infty$, applied with $\operatorname{wt}(e)\le D$, it bounds the residual $\mathcal H\tilde e$ by at most $2^kD$ nonzero entries of absolute value at most $1$, so the target lies within $\ell_p$-distance $(2^kD)^{1/p}$ of the lattice (within $1$ for $p=\infty$).
--
--   **Formalization Note.** The lift is `liftZMod`, binarity is `IsBinary`, block sparsity is `AtMostOnePerBlock Prod.fst` (the blocks are the fibres of the first projection), and the weight is Mathlib's `hammingNorm`. Lean writes the prime as `p`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Lemma B.2 (\label{lem:embeddings}) and of Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Conversions/Lattices.lean, LatticePrepro.blockHad_lift_bound

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro
open Finset
variable {p : ℕ} [Fact p.Prime] {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ}

theorem LatticePrepro.blockHad_lift_bound {e : β × Hadamard.Idx k → ZMod p} (hb : IsBinary e)
    (h1 : AtMostOnePerBlock Prod.fst e) :
    (∀ su, |Hadamard.blockHad k (liftZMod e) su| ≤ 1) ∧
    (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card ≤
      hammingNorm e * 2 ^ k := by sorry
