-- Prove2me | Theorems.Thm_MinCostMaj_theorem_A_6
-- name    : MinCostMaj.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:22.955958+00:00
-- url     : https://prove2.me/theorems/81762ea7-9db5-410a-82d0-a4881146691d
-- title:
--   Theorem A.6 — conservative commutative binary polymorphisms and the digraph $G(I)$
-- statement:
--   Let $I$ be a finite binary instance: every constraint $R\in\mathcal R_{xy}$ is a relation $R\subseteq A_x\times A_y$ between the potatoes, and $\mathcal R_{yx}$ consists of the opposite readings of $\mathcal R_{xy}$. Then
--   $$I\text{ has a conservative commutative binary polymorphism}\iff\text{no two dual vertices }(a,b;x),(b,a;x)\text{ of }G(I)\text{ are in the same strongly connected component.}$$
--
--   This criterion supplies the polymorphism used to handle the linked case of Theorem A.1, and a dual pair in one component yields Item 3 of Theorem 4.1.
--
--   Differences from the source:
--   - reading: binary instance → every constraint lies in A_x × A_y (`IsBinary`), finite variables and values, opposite readings (`IsSymm`); reason: f_x : A_x² → A_x must apply to the pairs of the constraints; instances are finite and follow §3's convention
--   - encoding: family {f_x : A_x² → A_x} → f : V → D → D → D with conservativity and commutativity on A_x; reason: only the values on A_x × A_x matter
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem A.6, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BinPol

namespace MinCostMaj

/-- **Theorem A.6**, p.14 (PDF p.15; proof pp.18–19).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem A.6, p.14: "A binary instance I has a conservative commutative binary polymorphism if
and only if no dual vertices belong to the same strongly connected component of G(I)."

**Formalization Note.** A binary instance is a finite instance (`Finite V`, `Finite D`) whose
constraints are relations between the potatoes (`IsBinary`, as `fₓ : A²ₓ → Aₓ` requires) and
which follows the opposite-readings convention of §3 (`IsSymm`). Arc consistency is not assumed.
Strongly connected components are classes of mutual reachability in `G(I)`. -/
theorem theorem_A_6 {V D : Type*} [Finite V] [Finite D] (I : BinInst V D) (hS : I.IsSymm)
    (hB : I.IsBinary) :
    (∃ f : V → D → D → D, I.IsConsCommBinPol f) ↔ I.NoDualSameSCC := by sorry

end MinCostMaj
