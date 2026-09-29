-- Prove2me | Theorems.Thm_ModPForms_nonempty_ssDatum_algebraicClosure
-- name    : ModPForms.nonempty_ssDatum_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6ad6b7d3-f5af-53e7-a987-e9e92752507a
-- title:
--   Existence of a supersingular datum over 𝔽̄ₚ
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N'$ be a nonzero natural number with $p \nmid N'$, and let $S_0$ be any set of natural numbers with $p \in S_0$. Then the structure [`ModPForms.SSDatum p N' S₀ (AlgebraicClosure (ZMod p))`](def/ModPForms_SSDatum.html#L7) is inhabited; writing $F = \overline{\mathbb{F}}_p$ and $M_k =$ `modPMod N' k F` for the $F$-span inside $F[[q]]$ of the reductions of $q$-expansions of integral-coefficient weight-$k$ modular forms on $\Gamma_0(N')$, such an inhabitant consists of: a family of $F$-vector spaces $S_k$ indexed by $k \in \mathbb{Z}$; $F$-linear endomorphisms $T_{k,\ell}$ of $S_k$ for all $k \in \mathbb{Z}$ and all natural numbers $\ell$; the stability of $M_k$, for $k \ge p+2$, under the explicit $q$-expansion operator `heckePS` $k$ $\ell$, $a_n \mapsto a_{n\ell} + \ell^{k-1}a_{n/\ell}$ (the second term only when $\ell \mid n$), for every prime $\ell \nmid N'$ with $\ell \notin S_0$; $F$-linear maps $\mathrm{res}_k : M_k \to S_k$ for $k \ge p+2$ intertwining `heckePS` $k$ $\ell$ with $T_{k,\ell}$ at those $\ell$, and with the property that $\mathrm{res}_k(\varphi) = 0$ implies $\varphi \in M_{k-(p-1)}$; $F$-linear isomorphisms $B_k : S_k \cong S_{k+p+1}$ for $k \ge 1$ with $T_{k+p+1,\ell} \circ B_k = \ell \cdot (B_k \circ T_{k,\ell})$ at those $\ell$; and a pullback property: for $1 \le k' \le p+1$, every nonzero $v \in S_{k'}$ which is a simultaneous eigenvector, $T_{k',\ell}v = \mu_\ell v$ for all those $\ell$, admits $k''$ with $2 \le k'' \le p+1$, an integer $j \ge 0$, a nonzero $\psi \in M_{k''}$ and $\nu : \mathbb{N} \to F$ with `heckePS` $k''$ $\ell$ $\psi = \nu_\ell \psi$ and $\nu_\ell = \ell^{j}\mu_\ell$ for all those $\ell$.
--
--   This packages the supersingular theory of $X_0(N')$ in characteristic $p$ (Hecke action on the supersingular space, restriction of mod-$p$ forms, multiplication by a weight-$(p+1)$ element, and the weight window $2 \le k'' \le p+1$) into the single data structure used by the weight-lowering step of Serre's conjecture in the mod-$p$ setting. It is the existence input for [`ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure`](thm.html#ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure), which extracts from the datum an eigenform of weight at most $p+1$ with the given eigensystem up to a power-of-$\ell$ twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_nonempty_ssDatum_algebraicClosure.lean

import Definitions.Def_ModPForms_SSDatum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.nonempty_ssDatum_algebraicClosure
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀p : p ∈ S₀) :
    Nonempty (ModPForms.SSDatum p N' S₀ (AlgebraicClosure (ZMod p))) := by sorry
