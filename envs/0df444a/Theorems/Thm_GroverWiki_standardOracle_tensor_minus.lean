-- Prove2me | Theorems.Thm_GroverWiki_standardOracle_tensor_minus
-- name    : GroverWiki.standardOracle_tensor_minus
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:34:17.72602+00:00
-- url     : https://prove2.me/theorems/f521aafb-4404-4b04-afe5-7828c0032296
-- title:
--   Alternative oracle: $U_f(|x\rangle\otimes|-\rangle) = (U_\omega|x\rangle)\otimes|-\rangle$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$, let $U_f|x\rangle|y\rangle = |x\rangle|y\oplus f(x)\rangle$ be the standard oracle on $\mathbb C^N\otimes\mathbb C^2$, let $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$ be the phase oracle, and let $|-\rangle = \frac{1}{\sqrt2}(|0\rangle - |1\rangle)$. Then for every basis state $|x\rangle$,
--
--   $$U_f\bigl(|x\rangle\otimes|-\rangle\bigr) = \bigl(U_\omega|x\rangle\bigr)\otimes|-\rangle .$$
--
--   This shows that Grover's algorithm can be run with either oracle: given $U_f$, one keeps an ancillary qubit in the state $|-\rangle$ and applies $U_f$ in place of $U_\omega$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Alternative oracle definition" (PDF p. 3)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Alternative oracle definition: on `|x⟩ ⊗ |−⟩`, the standard oracle `U_f` acts as the phase
oracle `U_ω` on the main register, leaving the ancilla in `|−⟩`. -/
theorem standardOracle_tensor_minus {N : ℕ} (f : Fin N → Fin 2) (x : Fin N) :
    standardOracle f *ᵥ tensorKet (ket x) minusState =
      tensorKet (phaseOracle f *ᵥ ket x) minusState := by sorry

end GroverWiki
