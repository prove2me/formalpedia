-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_circuit_collapse
-- name    : HypercliqueAC0.FixedDepth.circuit_collapse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:35.01395+00:00
-- url     : https://prove2.me/theorems/6f5da237-1575-592c-a88d-a82cfecbf2a1
-- title:
--   Constant-depth circuits collapse under random restrictions
-- statement:
--   Let $X$ be a finite set, let $h,w\ge1$ be integers, and let $C$ be a De Morgan circuit (AND and OR gates of unbounded fan-in over literals and constants) on the variables $(x_e)_{e\in X}$ of depth at most $h$ with $G(C)$ gates, computing $f$. Put
--
--   $$q=\frac1{32}\Bigl(\frac1{32w}\Bigr)^{h-1}.$$
--
--   Then a $q$-random restriction $\rho$ satisfies
--
--   $$\Pr_{\rho\sim\mathcal R_q}\bigl[\mathrm{DT}(f|_\rho)>w\bigr]\le G(C)\,2^{-w}.$$
--
--   This is the depth-reduction consequence of Håstad's switching lemma: a random restriction with star probability about $w^{-(h-1)}$ turns a depth-$h$ circuit into a decision tree of depth $w$, except with probability at most $G(C)2^{-w}$. Combined with the restriction bound on Fourier tails it gives exponential Fourier concentration of constant-depth circuits.
--
--   **Formalization Note** Circuits are `MantriCVQ.ACCircuit`; depth counts the gates on a longest path to the output, and $G(C)$ is the length of the gate list.
-- source:
--   Håstad, Almost optimal lower bounds for small depth circuits, STOC 1986 (layer-by-layer application of the switching lemma); Linial, Mansour, Nisan, J. ACM 40 (1993), Lemma 8 and its proof; used for Theorem 3.2 of Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf.

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem circuit_collapse {X : Type} [Fintype X] (h w : ℕ) (hh : 1 ≤ h) (hw : 1 ≤ w)
    (C : MantriCVQ.ACCircuit X) (hC : C.depth ≤ h) :
    restrictionProb ((1 / 32) * (1 / (32 * (w : ℝ))) ^ (h - 1))
        (fun ρ => ¬ DTDepthLE w (restrictFn ρ C.eval)) ≤
      (C.gates.length : ℝ) * (2 : ℝ) ^ (-(w : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth
