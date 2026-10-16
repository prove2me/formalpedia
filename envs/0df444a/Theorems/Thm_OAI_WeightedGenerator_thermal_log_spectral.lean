-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_thermal_log_spectral
-- name    : OAI.WeightedGenerator.thermal_log_spectral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:09.35004+00:00
-- url     : https://prove2.me/theorems/cfbc1676-4af8-4453-a2db-d619dde17068
-- title:
--   Spectral double-sum formula for the weighted thermal generator paired with a logarithm-type operator
-- statement:
--   Fix a number $n\in\mathbb{N}$ of bosonic modes and let $\mathcal F_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ be the $n$-mode Fock space with number basis $(|k\rangle)_{k\in\mathbb{N}^n}$; inner products $\langle\cdot,\cdot\rangle$ are conjugate-linear in the first argument. For $k\in\mathbb{N}^n$ write $|k|=\sum_j k_j$, $\nu(k)=1+|k|$, and let $e_j$ be the $j$-th unit vector of $\mathbb{N}^n$. For $m\in\mathbb{N}$, $\nu^{-m}$ denotes the bounded diagonal operator $(\nu^{-m}y)(k)=\nu(k)^{-m}y(k)$.
--
--   For families $u=(u_i)_{i\in I}$, $v=(v_i)_{i\in I}$ in a Hilbert space with $\sum_i\|u_i\|^2<\infty$ and $\sum_i\|v_i\|^2<\infty$ write $\Omega(u,v)=\sum_i|u_i\rangle\langle v_i|$ for the (norm-convergent) sum of rank-one operators $y\mapsto\langle v_i,y\rangle u_i$, and for a bounded operator $Z$ write $\langle\!\langle u,v\rangle\!\rangle_Z=\sum_i\langle v_i,Zu_i\rangle$; for an operator $T$, $Tu$ is the family $(Tu_i)_i$.
--
--   For a mode $j$ let $A_j^-$ and $A_j^+$ be the bounded operators on $\mathcal F_n$ given by
--   $$
--   (A_j^-y)(k)=\frac{\nu(k)^2\sqrt{k_j+1}}{\nu(k+e_j)^3}\,y(k+e_j),\qquad (A_j^+y)(k+e_j)=\frac{\nu(k+e_j)^2\sqrt{k_j+1}}{\nu(k)^3}\,y(k),
--   $$
--   with $(A_j^+y)(k)=0$ whenever $k_j=0$ (formally $A_j^-=\nu^2a_j\nu^{-3}$ and $A_j^+=\nu^2a_j^\dagger\nu^{-3}$ with the annihilation and creation operators $a_j,a_j^\dagger$), and let $M_j^-$, $M_j^+$ be the diagonal operators $(M_j^-y)(k)=\frac{k_j}{\nu(k)}y(k)$ and $(M_j^+y)(k)=\frac{k_j+1}{\nu(k)}y(k)$. For a family $x$ and bounded $Z$ put
--   $$
--   \pi_j^\pm(x;Z)=\langle\!\langle A_j^\pm x,A_j^\pm x\rangle\!\rangle_Z-\tfrac12\Bigl(\langle\!\langle M_j^\pm x,\nu^{-1}x\rangle\!\rangle_Z+\langle\!\langle \nu^{-1}x,M_j^\pm x\rangle\!\rangle_Z\Bigr).
--   $$
--   and for $t\in\mathbb{R}$ let $P_t(x;Z)=\sum_j\bigl((t+1)\,\pi_j^-(x;Z)+t\,\pi_j^+(x;Z)\bigr)$ (the pairing of $Z$ with the weighted thermal generator at parameter $t$).
--
--   Let $(b_l)_{l\in J}$ be a Hilbert basis of $\mathcal F_n$, $p:J\to\mathbb{R}$ with $p_r>0$ for all $r$, and $x=(x_r)_{r\in J}$ with $\sum_r\|x_r\|^2<\infty$ and $\nu^{-3}x_r=\sqrt{p_r}\,b_r$ for every $r$. Let $S$ be a bounded symmetric operator and $c:J\to[0,\infty)$ such that
--   1. for every $y\in\mathcal F_n$, $\sum_l c_l\,|\langle b_l,\nu^{-2}y\rangle|^2=\operatorname{Re}\langle y,Sy\rangle$ (the series converging);
--   2. for every $r$, $S\,\nu^{-1}x_r=c_r\,\nu^{-5}x_r$.
--
--   For each mode $j$ define the lowering matrix
--   $$
--   \lambda^{(j)}_{lr}=\frac{\langle b_l,\,G_j\,\nu^{-2}x_r\rangle}{\sqrt{p_r}},\qquad (G_jy)(k)=\frac{\sqrt{k_j+1}}{\nu(k+e_j)}\,y(k+e_j),
--   $$
--   so that $G_j$ is formally $a_j\nu^{-1}$ and $\lambda^{(j)}$ plays the role of the matrix of the annihilation operator $a_j$ in the basis $b$.
--
--   **Theorem.** For every $t\in\mathbb{R}$,
--   $$
--   \operatorname{Re}P_t(x;S)=\sum_{j}\ \sum_{(l,r)\in J\times J}(c_l-c_r)\bigl((t+1)\,p_r-t\,p_l\bigr)\,\bigl|\lambda^{(j)}_{lr}\bigr|^2 .
--   $$
--
--   In the intended application $b$ is an eigenbasis of a state with eigenvalues $p_l$, $c_l=-\log p_l$ and $S$ is a weighted logarithm of the state, so that the left side is the real part of the pairing of the thermal generator with $-\log\rho$; the formula writes it as an explicit spectral double sum whose sign structure can be analysed term by term.
--
--   **Formalization Note** $P_t$ is `WeightedGenerator.pairing t x S`, $\nu^{-m}$ is `inverseWeight m`, $\lambda^{(j)}_{lr}$ is `loweringEntry b p x j l r`. The inner sums over $J\times J$ are Lean `tsum`s; their summability is established in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Gibbs.lean#L844-L875

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
variable {n : ℕ} {J : Type*}

theorem OAI.WeightedGenerator.thermal_log_spectral (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (t : ℝ) :
    (pairing t x S).re = ∑ j, ∑' a : J × J,
      (c a.1-c a.2)*((t+1)*p a.2-t*p a.1)*‖loweringEntry b p x j a.1 a.2‖^2 := by sorry
