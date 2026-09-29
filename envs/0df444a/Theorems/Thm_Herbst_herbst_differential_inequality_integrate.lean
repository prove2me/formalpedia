-- Prove2me | Theorems.Thm_Herbst_herbst_differential_inequality_integrate
-- name    : Herbst.herbst_differential_inequality_integrate
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T02:21:03.943636+00:00
-- url     : https://prove2.me/theorems/eadbe34b-3c8a-4925-86e8-2c2ef967642e
-- title:
--   Herbst's argument: integrating the entropy differential inequality
-- statement:
--   **Herbst's argument, calculus core (the entropy-method MGF-from-entropy integration step).** Let $g:\mathbb R\to\mathbb R$ be continuous on $[0,\lambda]$, with a right derivative $g'$ on $[0,\lambda)$ (i.e. $g$ has the within-derivative $g'(x)$ on $[x,\infty)$ at each $x\in[0,\lambda)$) satisfying $g'(x)\le C$. Then $g(\lambda)\le g(0)+C\,\lambda$.
--
--   **Role in the entropy method.** This is exactly the integration step in Herbst's argument (Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, §5.2, proof of Theorem 5.3). A logarithmic Sobolev inequality applied to $e^{\lambda Z}$ yields the differential inequality $\lambda G'(\lambda)-G(\lambda)\le\psi(\lambda)$ for the log-MGF $G(\lambda)=\log\mathbb E e^{\lambda Z}$; dividing by $\lambda^2$ identifies the left side as $(G(\lambda)/\lambda)'$, so with $g(\lambda)=G(\lambda)/\lambda$ (and $g(0)=\mathbb E Z$ by l'Hôpital) the LSI bound $g'\le C$ integrates to the slope bound $G(\lambda)/\lambda\le \mathbb E Z+C\lambda$, hence the Gaussian-shaped MGF bound $G(\lambda)\le \mathbb E Z\,\lambda+C\lambda^2$. The same template (with a modified LSI giving a non-quadratic $\psi$) yields the Bennett/Bousquet inequality for suprema of empirical processes (BLM Ch.12). This isolated, source-faithful real-analysis lemma is the reusable Herbst integration brick; the Chern off MGF$\Rightarrow$tail closure is already available in Mathlib (`ProbabilityTheory.measure_ge_le_exp_mul_mgf`), and the remaining irreducible step is the (modified) log-Sobolev inequality itself.
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities: A Nonasymptotic Theory of Independence, Oxford University Press 2013, Section 5.2 (Herbst's argument), proof of Theorem 5.3, and the general entropy-method pattern of Chapters 6 and 12. Original: I. Herbst (unpublished); M. Ledoux, The Concentration of Measure Phenomenon, AMS 2001.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
open Set Filter Topology

theorem Herbst.herbst_differential_inequality_integrate
    (g g' : ℝ → ℝ) (m C lam : ℝ)
    (hlam : 0 ≤ lam)
    (hg_cont : ContinuousOn g (Set.Icc 0 lam))
    (hg0 : g 0 = m)
    (hg_deriv : ∀ x ∈ Set.Ico (0 : ℝ) lam, HasDerivWithinAt g (g' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) lam, g' x ≤ C) :
    g lam ≤ m + C * lam := by sorry
