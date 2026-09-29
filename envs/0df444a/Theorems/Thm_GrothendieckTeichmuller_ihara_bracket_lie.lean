-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_ihara_bracket_lie
-- name    : GrothendieckTeichmuller.ihara_bracket_lie
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:36:58.944408+00:00
-- url     : https://prove2.me/theorems/667223b8-24ad-4f98-9148-a1a774d829ea
-- title:
--   Corollary 7.1 — the Ihara (Poisson) bracket is a Lie bracket
-- statement:
--   On the free Lie algebra $\mathbb F(x,y)$ over $\mathbb Q$, the Ihara (Poisson) bracket
--
--   $$\{f,g\} = [f,g] + D_f g - D_g f, \qquad D_f x = 0,\ D_f y = [y,f],$$
--
--   is a Lie bracket. Explicitly, four assertions hold:
--
--   1. additivity in the first argument: $\{f+g, h\} = \{f,h\} + \{g,h\}$;
--   2. homogeneity in the first argument: $\{c\,f, g\} = c\,\{f,g\}$ for $c \in \mathbb Q$;
--   3. antisymmetry: $\{f,g\} = -\{g,f\}$;
--   4. the Jacobi identity: $\{f,\{g,h\}\} + \{g,\{h,f\}\} + \{h,\{f,g\}\} = 0$.
--
--   Together with antisymmetry, items 1 and 2 give bilinearity. This is the structure with respect to which $\mathfrak{grt}_1$ is a Lie algebra, and with respect to which the Deligne-Drinfeld-Ihara conjecture asserts freeness.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.3, p. 55 (Lemma 7.2, Corollary 7.1, Remarks 7.1 and 7.2); Remark 4.4, p. 47

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem ihara_bracket_lie :
    (∀ f g h : Lxy, iharaBracket (f + g) h = iharaBracket f h + iharaBracket g h) ∧
    (∀ (c : ℚ) (f g : Lxy), iharaBracket (c • f) g = c • iharaBracket f g) ∧
    (∀ f g : Lxy, iharaBracket f g = -iharaBracket g f) ∧
    (∀ f g h : Lxy, iharaBracket f (iharaBracket g h) + iharaBracket g (iharaBracket h f) +
      iharaBracket h (iharaBracket f g) = 0) := by sorry

end GrothendieckTeichmuller
