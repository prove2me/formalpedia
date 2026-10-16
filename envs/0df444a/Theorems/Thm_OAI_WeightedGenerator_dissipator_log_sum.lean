-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_dissipator_log_sum
-- name    : OAI.WeightedGenerator.dissipator_log_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:05:39.69071+00:00
-- url     : https://prove2.me/theorems/98987828-01b9-45f6-8940-8431ae82d4f5
-- title:
--   Real part of a weighted dissipator pairing with a logarithm-type operator as a spectral double sum
-- statement:
--   Fix a number $n\in\mathbb{N}$ of bosonic modes and let $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$; inner products $\langle\cdot,\cdot\rangle$ are conjugate-linear in the first argument. For $k\in\mathbb{N}^n$ write $|k|=\sum_j k_j$, $\nu(k)=1+|k|$, and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. For $m\in\mathbb{N}$, $\nu^{-m}$ denotes the bounded diagonal operator $(\nu^{-m}y)(k)=\nu(k)^{-m}y(k)$.
--
--   For families $u=(u_i)_{i\in I}$, $v=(v_i)_{i\in I}$ in a Hilbert space with $\sum_i\|u_i\|^2<\infty$ and $\sum_i\|v_i\|^2<\infty$ write $\Omega(u,v)=\sum_i|u_i\rangle\langle v_i|$ for the (norm-convergent) sum of rank-one operators $y\mapsto\langle v_i,y\rangle u_i$, and for a bounded operator $Z$ write $\langle\!\langle u,v\rangle\!\rangle_Z=\sum_i\langle v_i,Zu_i\rangle$; for an operator $T$, $Tu$ is the family $(Tu_i)_i$.
--
--   For a mode $j$ let $A_j^-$ and $A_j^+$ be the bounded operators on $\mathcal F_n$ given by
--   $$
--   (A_j^-y)(k)=\frac{\nu(k)^2\sqrt{k_j+1}}{\nu(k+e_j)^3}\,y(k+e_j),\qquad (A_j^+y)(k+e_j)=\frac{\nu(k+e_j)^2\sqrt{k_j+1}}{\nu(k)^3}\,y(k),
--   $$
--   with $(A_j^+y)(k)=0$ whenever $k_j=0$ (formally $A_j^-=\nu^2a_j\nu^{-3}$ and $A_j^+=\nu^2a_j^\dagger\nu^{-3}$ with the annihilation and creation operators $a_j,a_j^\dagger$), and let $M_j^-$, $M_j^+$ be the diagonal operators $(M_j^-y)(k)=\frac{k_j}{\nu(k)}y(k)$ and $(M_j^+y)(k)=\frac{k_j+1}{\nu(k)}y(k)$.
--
--   Let $G_j^-$ and $G_j^+$ be the bounded weighted ladder operators of mode $j$,
--   $$
--   (G_j^-y)(k)=\frac{\sqrt{k_j+1}}{\nu(k+e_j)}\,y(k+e_j),\qquad (G_j^+y)(k+e_j)=\frac{\sqrt{k_j+1}}{\nu(k)}\,y(k),\quad (G_j^+y)(k)=0\text{ if }k_j=0,
--   $$
--   formally $G_j^-=a_j\nu^{-1}$ and $G_j^+=a_j^\dagger\nu^{-1}$.
--
--   Let $(b_l)_{l\in J}$ be a Hilbert basis of $\mathcal F_n$ and $x=(x_r)_{r\in J}$ a family indexed by the same set with $\sum_r\|x_r\|^2<\infty$. Let $S$ be a bounded symmetric operator on $\mathcal F_n$ and $c:J\to\mathbb{R}$ with $c_l\ge 0$ for all $l$, and assume
--   1. for every $y\in\mathcal F_n$, $\displaystyle\sum_{l\in J}c_l\,\bigl|\langle b_l,\nu^{-2}y\rangle\bigr|^2=\operatorname{Re}\langle y,Sy\rangle$ (the series converging);
--   2. for every $r\in J$, $S\,\nu^{-1}x_r=c_r\,\nu^{-5}x_r$.
--
--   Fix a mode $j$ and a sign $\sigma\in\{-,+\}$, and put $\gamma_{lr}=\langle b_l,\,G_j^\sigma\nu^{-2}x_r\rangle$ for $l,r\in J$.
--
--   **Theorem.** Under these hypotheses
--   $$
--   \operatorname{Re}\Bigl[\langle\!\langle A_j^\sigma x,A_j^\sigma x\rangle\!\rangle_S-\tfrac12\Bigl(\langle\!\langle M_j^\sigma x,\nu^{-1}x\rangle\!\rangle_S+\langle\!\langle \nu^{-1}x,M_j^\sigma x\rangle\!\rangle_S\Bigr)\Bigr]=\sum_{(l,r)\in J\times J}(c_l-c_r)\,|\gamma_{lr}|^2 .
--   $$
--
--   Hypothesis 1 says that, as a quadratic form, $S$ is formally $\nu^{-2}C\nu^{-2}$ for the operator $C=\sum_l c_l|b_l\rangle\langle b_l|$ diagonal in the basis $b$, and hypothesis 2 ties the vectors $x_r$ to the same diagonal data. The identity expresses the real part of one dissipator term of the weighted thermal generator, tested against such a logarithm-like operator, as a double sum over pairs of basis indices weighted by the differences $c_l-c_r$. It is the per-mode building block of a spectral formula for the generator paired with $-\log\rho$-type operators.
--
--   **Formalization Note** The sign is the Boolean `u` (`false` for $-$, `true` for $+$); $\gamma_{lr}$ is `spectralGain b x j u l r`, $G_j^\mp$ are `lowering j`/`raising j` (through `unweightedGain`), $A_j^\pm$ is `gain`, $M_j^\pm$ is `modeBound`, $\nu^{-m}$ is `inverseWeight m`. The right side is a Lean `tsum` over $J\times J$; the proof shows this family is summable, so it is a genuine sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Gibbs.lean#L580-L636

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs

open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem OAI.WeightedGenerator.dissipator_log_sum (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (u : Bool) :
    (CrossEnsemble.pairing (fun r => gain j u (x r)) (fun r => gain j u (x r)) S-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S+
        CrossEnsemble.pairing (fun r => inverseWeight 1 (x r)) (fun r => modeBound j u (x r)) S)).re =
      ∑' a : J × J, (c a.1-c a.2)*‖spectralGain b x j u a.1 a.2‖^2 := by sorry
