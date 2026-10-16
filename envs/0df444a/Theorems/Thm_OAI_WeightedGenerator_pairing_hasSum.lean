-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_pairing_hasSum
-- name    : OAI.WeightedGenerator.pairing_hasSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:04:15.915986+00:00
-- url     : https://prove2.me/theorems/b0ae9fdd-967c-442d-9041-acc97c0bb221
-- title:
--   Basis trace of $Z\,\mathcal L_r(x)$ for the weighted thermal generator equals its explicit pairing
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
--   Given a family $x=(x_i)_{i\in I}$ in $\mathcal F_n$ with $\sum_i\|x_i\|^2<\infty$ and $r\in\mathbb{R}$, define the weighted dissipators and the weighted generator
--   $$
--   D_j^\pm(x)=\Omega(A_j^\pm x,A_j^\pm x)-\tfrac12\bigl(\Omega(M_j^\pm x,\nu^{-1}x)+\Omega(\nu^{-1}x,M_j^\pm x)\bigr),\qquad \mathcal L_r(x)=\sum_{j}\bigl((r+1)\,D_j^-(x)+r\,D_j^+(x)\bigr),
--   $$
--   and, for a bounded operator $Z$ on $\mathcal F_n$, the scalar $P_r(x;Z)=\sum_j\bigl((r+1)\,\pi_j^-(x;Z)+r\,\pi_j^+(x;Z)\bigr)$, where
--   $$
--   \pi_j^\pm(x;Z)=\langle\!\langle A_j^\pm x,A_j^\pm x\rangle\!\rangle_Z-\tfrac12\Bigl(\langle\!\langle M_j^\pm x,\nu^{-1}x\rangle\!\rangle_Z+\langle\!\langle \nu^{-1}x,M_j^\pm x\rangle\!\rangle_Z\Bigr).
--   $$
--
--   **Theorem.** For every Hilbert basis $(b_k)_{k\in K}$ of $\mathcal F_n$, every $r\in\mathbb{R}$, every square-summable family $x$ as above and every bounded operator $Z$ on $\mathcal F_n$, the series below converges unconditionally and
--   $$
--   \sum_{k\in K}\bigl\langle b_k,\;Z\,\mathcal L_r(x)\,b_k\bigr\rangle=P_r(x;Z).
--   $$
--
--   The operator $\mathcal L_r(x)$ can be read as a bounded, number-weighted version of the thermal-noise (GKSL) generator with jump operators $a_j$ at rate $r+1$ and $a_j^\dagger$ at rate $r$, applied to the ensemble $\Omega(x,x)$. The theorem identifies the basis trace $\operatorname{Tr}(Z\,\mathcal L_r(x))$, computed in an arbitrary Hilbert basis, with the explicit ensemble formula $P_r(x;Z)$, which is independent of the basis.
--
--   **Formalization Note** The sign $\pm$ corresponds to the Boolean flag `upward` (`false` for $-$, `true` for $+$); $A_j^-$, $A_j^+$ are `gain j false`, `gain j true`, $M_j^\pm$ is `modeBound`, $\nu^{-m}$ is `inverseWeight m`, $\Omega$ is `CrossEnsemble.operator` and $\langle\!\langle\cdot,\cdot\rangle\!\rangle_Z$ is `CrossEnsemble.pairing`. Convergence is expressed with `HasSum`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Fock/Operators.lean#L671-L687

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

theorem OAI.WeightedGenerator.pairing_hasSum (b : HilbertBasis J ℂ (Fock n)) (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (generator r x (b k)))) (pairing r x Z) := by sorry
