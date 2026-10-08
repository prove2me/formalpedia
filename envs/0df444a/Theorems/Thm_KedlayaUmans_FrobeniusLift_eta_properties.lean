-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_eta_properties
-- name    : KedlayaUmans.FrobeniusLift.eta_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:18.205035+00:00
-- url     : https://prove2.me/theorems/62f96184-df38-4f6d-83ab-bae566405036
-- title:
--   §6, p. 18 — η has multiplicative order h − 1 and ηⁱ − ηʲ is invertible in R for i ≠ j < m
-- statement:
--   Let $p$ be a prime, $\mathbb F_q$ a finite field of characteristic $p$, and $P \in \mathbb F_p[W]$ irreducible over $\mathbb F_p$ of degree $c$, with $h = p^c$. Let $K = \mathbb F_p[W]/(P(W))$, $R = \mathbb F_q[W]/(P(W))$, and let $\eta$ be a primitive element of the field $K$, i.e. a generator of its multiplicative group, which has order $h - 1$. Let $m, d$ be natural numbers with $d \ge 1$ and $h > m^2 d$. Then, viewing $\eta$ in $R$ through $K \subseteq R$:
--
--   1. the multiplicative order of $\eta$ in $R$ is $h-1$;
--   2. for all $i \ne j$ in $\{0, 1, \dots, m-1\}$,
--   $$\eta^i - \eta^j \ \text{ is invertible in } R.$$
--
--   These are the two properties the construction of Section 6 requires of $\eta$; the second one is what makes interpolation at the nodes $\eta^0, \dots, \eta^{m-1}$ possible in the ring $R$, which need not be a field.
--
--   **Formalization Note** "Primitive element" is encoded as `IsPrimitiveRoot η (h - 1)`; since $|K| = p^c = h$, this says exactly that $\eta$ generates $K^\times$. The standing hypotheses $d \ge 1$, $m^2 d < h$ of Section 6 are kept; the second property only needs $m \le h-1$, which they imply.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 18, Section 6 (properties 1 and 2 of η; unnumbered)

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- §6, p. 18: a primitive element `η` of `𝔽_p[W]/(P(W))` has multiplicative order `h - 1` (also as an
element of `R`), and `η^i - η^j` is invertible in `R` for all `i ≠ j` in `{0, …, m-1}`. -/
theorem eta_properties (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) :
    orderOf (ι p F P η) = h p P - 1 ∧
      ∀ i j : Fin m, i ≠ j → IsUnit (ι p F P η ^ (i : ℕ) - ι p F P η ^ (j : ℕ)) := by sorry

end KedlayaUmans.FrobeniusLift
