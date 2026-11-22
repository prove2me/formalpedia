-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartzRpos_concrete
-- name    : MasulloGRH.expDecaySchwartzRpos_concrete
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T06:48:13.233724+00:00
-- url     : https://prove2.me/theorems/5fe42d6d-9829-4ccb-840c-2d588764fd1a
-- title:
--   Concrete description of $\mathcal S_I(\mathbb R_{>0})$ and its topology
-- statement:
--   Let $I\subset\mathbb R$ be non-empty, and write a function $\phi$ on $\mathbb R_{>0}$ in the coordinate $t=e^x$, so that $\phi$ becomes a function $x\mapsto\phi(e^x)$ on $\mathbb R$.
--
--   **Membership.** A function $\phi$ belongs to the space $\mathcal S_I(\mathbb R_{>0})$ of Schwartz–Bruhat functions with $I$-exponential decay (Definition D.3.2.1, in the formalization of Definition D.3.3.1 for the modulated group $(\mathbb R_{>0},\mathrm{id})$) if and only if, for every $a\in I$, the function
--   $$x\longmapsto e^{ax}\,\phi(e^x)$$
--   is a Schwartz function on $\mathbb R$.
--
--   **Topology.** The inductive topology of $\mathcal S_I(\mathbb R_{>0})$ (Definition D.3.3.3) is the projective topology of the weighted maps
--   $$T_a\colon\ \phi\longmapsto\bigl(x\mapsto e^{ax}\phi(e^x)\bigr)\in\mathcal S(\mathbb R),\qquad a\in I,$$
--   where $\mathcal S(\mathbb R)$ carries its usual Fréchet topology. That is, it is the coarsest topology making every $T_a$ continuous. In the Lean statement this is expressed for any family $w$ of maps that agree with $T_a$ for every $a\in I$.
--
--   **Why this holds.** For $G=\mathbb R_{>0}\cong\mathbb R$, the only open compactly generated subgroup is $G$ itself, and the only good subgroup (closed, with open and compactly generated annihilator in $\widehat G\cong\mathbb R$) is the trivial one. Every presentation of $G$ as an elementary abelian Lie group is a linear rescaling $\mathbb R\to\mathbb R$. Hence $\mathcal S(G)$ and $\mathcal S(G/\{1\})$ are the classical Schwartz space with its Fréchet topology, and the inductive limit in Definition D.3.3.3 has a single step, namely the projective topology of the $T_a$.
--
--   This identifies the source's space $\mathcal S_I(\mathbb R_{>0})$ (Definition D.3.2.1, p. 801) with the space used in the proof of Proposition D.3.2.5.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Proposition D.3.2.5 (p. 802) and Lemma D.3.1.2 (pp. 799-800); Definitions D.1.5.1, D.1.5.3, D.3.2.1, D.3.3.1, D.3.3.3.

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

open MeasureTheory

namespace MasulloGRH

theorem expDecaySchwartzRpos_concrete (I : Set ℝ) (hne : I.Nonempty) :
    (∀ f : Multiplicative ℝ → ℂ, f ∈ expDecaySubmodule (Multiplicative ℝ) rposModule I ↔
      ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        g x = (Real.exp (a * x) : ℂ) * f (Multiplicative.ofAdd x)) ∧
    ∀ w : ℝ → ExpDecaySchwartzRpos I → SchwartzMap ℝ ℂ,
      (∀ a ∈ I, ∀ (ϕ : ExpDecaySchwartzRpos I) (x : ℝ),
        w a ϕ x = (Real.exp (a * x) : ℂ) * ϕ.toFun (Multiplicative.ofAdd x)) →
      (inferInstance : TopologicalSpace (ExpDecaySchwartzRpos I)) =
        ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (w a) inferInstance := by sorry

end MasulloGRH
